import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0835

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7680 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7680) = g32p_row31_cosetRepresentatives 7680 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7680 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7680) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7680))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7680)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7680 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7680) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7680))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7680)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7681 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7681) = g32p_row31_cosetRepresentatives 7681 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7681 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7681) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7681))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7681)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7681 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7681) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7681))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7681)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7682 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7682) = g32p_row31_cosetRepresentatives 7682 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7682 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7682) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7682))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7682)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7682 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7682) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7682))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7682)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7683 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7683) = g32p_row31_cosetRepresentatives 7683 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7683 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7683) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7683))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7683)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7683 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7683) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7683))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7683)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7684 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7684) = g32p_row31_cosetRepresentatives 7684 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7684 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7684) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7684))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7684)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7684 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7684) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7684))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7684)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7685 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7685) = g32p_row31_cosetRepresentatives 7685 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7685 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7685) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7685))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7685)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7685 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7685) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7685))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7685)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7686 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7686) = g32p_row31_cosetRepresentatives 7686 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7686 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7686) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7686))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7686)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7686 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7686) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7686))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7686)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7687 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7687) = g32p_row31_cosetRepresentatives 7687 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7687 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7687) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7687))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7687)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7687 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7687) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7687))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7687)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7688 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7688) = g32p_row31_cosetRepresentatives 7688 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7688 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7688) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7688))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7688)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7688 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7688) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7688))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7688)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7689 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7689) = g32p_row31_cosetRepresentatives 7689 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7689 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7689) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7689))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7689)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7689 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7689) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7689))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7689)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7690 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7690) = g32p_row31_cosetRepresentatives 7690 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7690 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7690) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7690))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7690)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7690 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7690) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7690))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7690)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7691 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7691) = g32p_row31_cosetRepresentatives 7691 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7691 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7691) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7691))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7691)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7691 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7691) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7691))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7691)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7692 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7692) = g32p_row31_cosetRepresentatives 7692 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7692 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7692) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7692))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7692)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7692 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7692) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7692))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7692)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7693 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7693) = g32p_row31_cosetRepresentatives 7693 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7693 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7693) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7693))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7693)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7693 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7693) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7693))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7693)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7694 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7694) = g32p_row31_cosetRepresentatives 7694 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7694 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7694) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7694))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7694)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7694 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7694) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7694))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7694)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7695 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7695) = g32p_row31_cosetRepresentatives 7695 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7695 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7695) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7695))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7695)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7695 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7695) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7695))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7695)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0480 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 480 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 480 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7680
  · exact g32p_row31_cosetWord_7681
  · exact g32p_row31_cosetWord_7682
  · exact g32p_row31_cosetWord_7683
  · exact g32p_row31_cosetWord_7684
  · exact g32p_row31_cosetWord_7685
  · exact g32p_row31_cosetWord_7686
  · exact g32p_row31_cosetWord_7687
  · exact g32p_row31_cosetWord_7688
  · exact g32p_row31_cosetWord_7689
  · exact g32p_row31_cosetWord_7690
  · exact g32p_row31_cosetWord_7691
  · exact g32p_row31_cosetWord_7692
  · exact g32p_row31_cosetWord_7693
  · exact g32p_row31_cosetWord_7694
  · exact g32p_row31_cosetWord_7695

theorem g32p_row31_cosetGeneratorBlock_0480 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 480 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 480 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 480 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7680 s
  · exact g32p_row31_cosetGeneratorStep_7681 s
  · exact g32p_row31_cosetGeneratorStep_7682 s
  · exact g32p_row31_cosetGeneratorStep_7683 s
  · exact g32p_row31_cosetGeneratorStep_7684 s
  · exact g32p_row31_cosetGeneratorStep_7685 s
  · exact g32p_row31_cosetGeneratorStep_7686 s
  · exact g32p_row31_cosetGeneratorStep_7687 s
  · exact g32p_row31_cosetGeneratorStep_7688 s
  · exact g32p_row31_cosetGeneratorStep_7689 s
  · exact g32p_row31_cosetGeneratorStep_7690 s
  · exact g32p_row31_cosetGeneratorStep_7691 s
  · exact g32p_row31_cosetGeneratorStep_7692 s
  · exact g32p_row31_cosetGeneratorStep_7693 s
  · exact g32p_row31_cosetGeneratorStep_7694 s
  · exact g32p_row31_cosetGeneratorStep_7695 s

theorem g32p_row31_cosetBranchBlock_0480 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 480 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 480 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 480 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7680 s
  · exact g32p_row31_cosetBranchStep_7681 s
  · exact g32p_row31_cosetBranchStep_7682 s
  · exact g32p_row31_cosetBranchStep_7683 s
  · exact g32p_row31_cosetBranchStep_7684 s
  · exact g32p_row31_cosetBranchStep_7685 s
  · exact g32p_row31_cosetBranchStep_7686 s
  · exact g32p_row31_cosetBranchStep_7687 s
  · exact g32p_row31_cosetBranchStep_7688 s
  · exact g32p_row31_cosetBranchStep_7689 s
  · exact g32p_row31_cosetBranchStep_7690 s
  · exact g32p_row31_cosetBranchStep_7691 s
  · exact g32p_row31_cosetBranchStep_7692 s
  · exact g32p_row31_cosetBranchStep_7693 s
  · exact g32p_row31_cosetBranchStep_7694 s
  · exact g32p_row31_cosetBranchStep_7695 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7696 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7696) = g32p_row31_cosetRepresentatives 7696 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7696 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7696) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7696))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7696)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7696 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7696) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7696))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7696)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7697 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7697) = g32p_row31_cosetRepresentatives 7697 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7697 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7697) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7697))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7697)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7697 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7697) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7697))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7697)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7698 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7698) = g32p_row31_cosetRepresentatives 7698 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7698 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7698) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7698))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7698)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7698 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7698) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7698))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7698)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7699 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7699) = g32p_row31_cosetRepresentatives 7699 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7699 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7699) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7699))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7699)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7699 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7699) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7699))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7699)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7700 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7700) = g32p_row31_cosetRepresentatives 7700 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7700 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7700) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7700))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7700)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7700 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7700) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7700))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7700)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7701 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7701) = g32p_row31_cosetRepresentatives 7701 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7701 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7701) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7701))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7701)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7701 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7701) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7701))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7701)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7702 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7702) = g32p_row31_cosetRepresentatives 7702 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7702 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7702) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7702))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7702)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7702 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7702) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7702))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7702)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7703 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7703) = g32p_row31_cosetRepresentatives 7703 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7703 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7703) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7703))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7703)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7703 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7703) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7703))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7703)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7704 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7704) = g32p_row31_cosetRepresentatives 7704 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7704 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7704) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7704))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7704)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7704 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7704) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7704))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7704)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7705 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7705) = g32p_row31_cosetRepresentatives 7705 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7705 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7705) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7705))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7705)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7705 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7705) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7705))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7705)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7706 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7706) = g32p_row31_cosetRepresentatives 7706 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7706 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7706) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7706))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7706)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7706 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7706) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7706))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7706)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7707 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7707) = g32p_row31_cosetRepresentatives 7707 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7707 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7707) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7707))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7707)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7707 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7707) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7707))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7707)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7708 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7708) = g32p_row31_cosetRepresentatives 7708 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7708 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7708) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7708))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7708)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7708 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7708) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7708))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7708)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7709 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7709) = g32p_row31_cosetRepresentatives 7709 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7709 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7709) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7709))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7709)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7709 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7709) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7709))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7709)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7710 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7710) = g32p_row31_cosetRepresentatives 7710 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7710 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7710) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7710))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7710)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7710 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7710) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7710))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7710)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7711 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7711) = g32p_row31_cosetRepresentatives 7711 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7711 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7711) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7711))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7711)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7711 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7711) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7711))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7711)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0481 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 481 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 481 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7696
  · exact g32p_row31_cosetWord_7697
  · exact g32p_row31_cosetWord_7698
  · exact g32p_row31_cosetWord_7699
  · exact g32p_row31_cosetWord_7700
  · exact g32p_row31_cosetWord_7701
  · exact g32p_row31_cosetWord_7702
  · exact g32p_row31_cosetWord_7703
  · exact g32p_row31_cosetWord_7704
  · exact g32p_row31_cosetWord_7705
  · exact g32p_row31_cosetWord_7706
  · exact g32p_row31_cosetWord_7707
  · exact g32p_row31_cosetWord_7708
  · exact g32p_row31_cosetWord_7709
  · exact g32p_row31_cosetWord_7710
  · exact g32p_row31_cosetWord_7711

theorem g32p_row31_cosetGeneratorBlock_0481 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 481 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 481 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 481 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7696 s
  · exact g32p_row31_cosetGeneratorStep_7697 s
  · exact g32p_row31_cosetGeneratorStep_7698 s
  · exact g32p_row31_cosetGeneratorStep_7699 s
  · exact g32p_row31_cosetGeneratorStep_7700 s
  · exact g32p_row31_cosetGeneratorStep_7701 s
  · exact g32p_row31_cosetGeneratorStep_7702 s
  · exact g32p_row31_cosetGeneratorStep_7703 s
  · exact g32p_row31_cosetGeneratorStep_7704 s
  · exact g32p_row31_cosetGeneratorStep_7705 s
  · exact g32p_row31_cosetGeneratorStep_7706 s
  · exact g32p_row31_cosetGeneratorStep_7707 s
  · exact g32p_row31_cosetGeneratorStep_7708 s
  · exact g32p_row31_cosetGeneratorStep_7709 s
  · exact g32p_row31_cosetGeneratorStep_7710 s
  · exact g32p_row31_cosetGeneratorStep_7711 s

theorem g32p_row31_cosetBranchBlock_0481 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 481 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 481 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 481 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7696 s
  · exact g32p_row31_cosetBranchStep_7697 s
  · exact g32p_row31_cosetBranchStep_7698 s
  · exact g32p_row31_cosetBranchStep_7699 s
  · exact g32p_row31_cosetBranchStep_7700 s
  · exact g32p_row31_cosetBranchStep_7701 s
  · exact g32p_row31_cosetBranchStep_7702 s
  · exact g32p_row31_cosetBranchStep_7703 s
  · exact g32p_row31_cosetBranchStep_7704 s
  · exact g32p_row31_cosetBranchStep_7705 s
  · exact g32p_row31_cosetBranchStep_7706 s
  · exact g32p_row31_cosetBranchStep_7707 s
  · exact g32p_row31_cosetBranchStep_7708 s
  · exact g32p_row31_cosetBranchStep_7709 s
  · exact g32p_row31_cosetBranchStep_7710 s
  · exact g32p_row31_cosetBranchStep_7711 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7712 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7712) = g32p_row31_cosetRepresentatives 7712 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7712 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7712) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7712))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7712)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7712 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7712) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7712))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7712)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7713 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7713) = g32p_row31_cosetRepresentatives 7713 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7713 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7713) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7713))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7713)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7713 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7713) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7713))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7713)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7714 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7714) = g32p_row31_cosetRepresentatives 7714 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7714 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7714) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7714))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7714)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7714 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7714) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7714))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7714)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7715 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7715) = g32p_row31_cosetRepresentatives 7715 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7715 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7715) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7715))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7715)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7715 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7715) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7715))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7715)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7716 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7716) = g32p_row31_cosetRepresentatives 7716 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7716 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7716) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7716))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7716)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7716 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7716) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7716))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7716)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7717 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7717) = g32p_row31_cosetRepresentatives 7717 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7717 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7717) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7717))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7717)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7717 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7717) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7717))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7717)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7718 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7718) = g32p_row31_cosetRepresentatives 7718 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7718 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7718) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7718))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7718)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7718 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7718) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7718))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7718)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7719 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7719) = g32p_row31_cosetRepresentatives 7719 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7719 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7719) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7719))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7719)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7719 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7719) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7719))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7719)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7720 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7720) = g32p_row31_cosetRepresentatives 7720 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7720 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7720) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7720))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7720)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7720 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7720) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7720))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7720)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7721 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7721) = g32p_row31_cosetRepresentatives 7721 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7721 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7721) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7721))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7721)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7721 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7721) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7721))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7721)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7722 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7722) = g32p_row31_cosetRepresentatives 7722 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7722 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7722) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7722))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7722)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7722 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7722) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7722))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7722)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7723 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7723) = g32p_row31_cosetRepresentatives 7723 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7723 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7723) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7723))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7723)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7723 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7723) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7723))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7723)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7724 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7724) = g32p_row31_cosetRepresentatives 7724 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7724 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7724) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7724))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7724)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7724 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7724) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7724))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7724)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7725 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7725) = g32p_row31_cosetRepresentatives 7725 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7725 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7725) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7725))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7725)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7725 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7725) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7725))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7725)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7726 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7726) = g32p_row31_cosetRepresentatives 7726 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7726 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7726) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7726))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7726)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7726 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7726) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7726))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7726)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7727 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7727) = g32p_row31_cosetRepresentatives 7727 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7727 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7727) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7727))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7727)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7727 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7727) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7727))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7727)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0482 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 482 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 482 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7712
  · exact g32p_row31_cosetWord_7713
  · exact g32p_row31_cosetWord_7714
  · exact g32p_row31_cosetWord_7715
  · exact g32p_row31_cosetWord_7716
  · exact g32p_row31_cosetWord_7717
  · exact g32p_row31_cosetWord_7718
  · exact g32p_row31_cosetWord_7719
  · exact g32p_row31_cosetWord_7720
  · exact g32p_row31_cosetWord_7721
  · exact g32p_row31_cosetWord_7722
  · exact g32p_row31_cosetWord_7723
  · exact g32p_row31_cosetWord_7724
  · exact g32p_row31_cosetWord_7725
  · exact g32p_row31_cosetWord_7726
  · exact g32p_row31_cosetWord_7727

theorem g32p_row31_cosetGeneratorBlock_0482 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 482 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 482 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 482 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7712 s
  · exact g32p_row31_cosetGeneratorStep_7713 s
  · exact g32p_row31_cosetGeneratorStep_7714 s
  · exact g32p_row31_cosetGeneratorStep_7715 s
  · exact g32p_row31_cosetGeneratorStep_7716 s
  · exact g32p_row31_cosetGeneratorStep_7717 s
  · exact g32p_row31_cosetGeneratorStep_7718 s
  · exact g32p_row31_cosetGeneratorStep_7719 s
  · exact g32p_row31_cosetGeneratorStep_7720 s
  · exact g32p_row31_cosetGeneratorStep_7721 s
  · exact g32p_row31_cosetGeneratorStep_7722 s
  · exact g32p_row31_cosetGeneratorStep_7723 s
  · exact g32p_row31_cosetGeneratorStep_7724 s
  · exact g32p_row31_cosetGeneratorStep_7725 s
  · exact g32p_row31_cosetGeneratorStep_7726 s
  · exact g32p_row31_cosetGeneratorStep_7727 s

theorem g32p_row31_cosetBranchBlock_0482 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 482 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 482 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 482 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7712 s
  · exact g32p_row31_cosetBranchStep_7713 s
  · exact g32p_row31_cosetBranchStep_7714 s
  · exact g32p_row31_cosetBranchStep_7715 s
  · exact g32p_row31_cosetBranchStep_7716 s
  · exact g32p_row31_cosetBranchStep_7717 s
  · exact g32p_row31_cosetBranchStep_7718 s
  · exact g32p_row31_cosetBranchStep_7719 s
  · exact g32p_row31_cosetBranchStep_7720 s
  · exact g32p_row31_cosetBranchStep_7721 s
  · exact g32p_row31_cosetBranchStep_7722 s
  · exact g32p_row31_cosetBranchStep_7723 s
  · exact g32p_row31_cosetBranchStep_7724 s
  · exact g32p_row31_cosetBranchStep_7725 s
  · exact g32p_row31_cosetBranchStep_7726 s
  · exact g32p_row31_cosetBranchStep_7727 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7728 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7728) = g32p_row31_cosetRepresentatives 7728 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7728 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7728) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7728))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7728)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7728 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7728) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7728))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7728)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7729 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7729) = g32p_row31_cosetRepresentatives 7729 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7729 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7729) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7729))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7729)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7729 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7729) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7729))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7729)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7730 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7730) = g32p_row31_cosetRepresentatives 7730 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7730 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7730) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7730))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7730)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7730 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7730) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7730))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7730)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7731 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7731) = g32p_row31_cosetRepresentatives 7731 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7731 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7731) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7731))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7731)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7731 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7731) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7731))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7731)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7732 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7732) = g32p_row31_cosetRepresentatives 7732 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7732 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7732) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7732))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7732)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7732 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7732) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7732))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7732)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7733 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7733) = g32p_row31_cosetRepresentatives 7733 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7733 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7733) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7733))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7733)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7733 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7733) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7733))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7733)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7734 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7734) = g32p_row31_cosetRepresentatives 7734 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7734 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7734) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7734))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7734)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7734 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7734) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7734))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7734)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7735 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7735) = g32p_row31_cosetRepresentatives 7735 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7735 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7735) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7735))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7735)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7735 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7735) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7735))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7735)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7736 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7736) = g32p_row31_cosetRepresentatives 7736 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7736 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7736) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7736))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7736)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7736 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7736) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7736))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7736)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7737 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7737) = g32p_row31_cosetRepresentatives 7737 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7737 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7737) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7737))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7737)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7737 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7737) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7737))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7737)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7738 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7738) = g32p_row31_cosetRepresentatives 7738 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7738 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7738) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7738))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7738)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7738 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7738) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7738))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7738)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7739 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7739) = g32p_row31_cosetRepresentatives 7739 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7739 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7739) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7739))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7739)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7739 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7739) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7739))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7739)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7740 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7740) = g32p_row31_cosetRepresentatives 7740 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7740 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7740) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7740))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7740)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7740 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7740) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7740))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7740)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7741 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7741) = g32p_row31_cosetRepresentatives 7741 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7741 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7741) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7741))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7741)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7741 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7741) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7741))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7741)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7742 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7742) = g32p_row31_cosetRepresentatives 7742 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7742 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7742) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7742))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7742)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7742 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7742) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7742))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7742)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7743 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7743) = g32p_row31_cosetRepresentatives 7743 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7743 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7743) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7743))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7743)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7743 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7743) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7743))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7743)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0483 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 483 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 483 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7728
  · exact g32p_row31_cosetWord_7729
  · exact g32p_row31_cosetWord_7730
  · exact g32p_row31_cosetWord_7731
  · exact g32p_row31_cosetWord_7732
  · exact g32p_row31_cosetWord_7733
  · exact g32p_row31_cosetWord_7734
  · exact g32p_row31_cosetWord_7735
  · exact g32p_row31_cosetWord_7736
  · exact g32p_row31_cosetWord_7737
  · exact g32p_row31_cosetWord_7738
  · exact g32p_row31_cosetWord_7739
  · exact g32p_row31_cosetWord_7740
  · exact g32p_row31_cosetWord_7741
  · exact g32p_row31_cosetWord_7742
  · exact g32p_row31_cosetWord_7743

theorem g32p_row31_cosetGeneratorBlock_0483 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 483 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 483 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 483 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7728 s
  · exact g32p_row31_cosetGeneratorStep_7729 s
  · exact g32p_row31_cosetGeneratorStep_7730 s
  · exact g32p_row31_cosetGeneratorStep_7731 s
  · exact g32p_row31_cosetGeneratorStep_7732 s
  · exact g32p_row31_cosetGeneratorStep_7733 s
  · exact g32p_row31_cosetGeneratorStep_7734 s
  · exact g32p_row31_cosetGeneratorStep_7735 s
  · exact g32p_row31_cosetGeneratorStep_7736 s
  · exact g32p_row31_cosetGeneratorStep_7737 s
  · exact g32p_row31_cosetGeneratorStep_7738 s
  · exact g32p_row31_cosetGeneratorStep_7739 s
  · exact g32p_row31_cosetGeneratorStep_7740 s
  · exact g32p_row31_cosetGeneratorStep_7741 s
  · exact g32p_row31_cosetGeneratorStep_7742 s
  · exact g32p_row31_cosetGeneratorStep_7743 s

theorem g32p_row31_cosetBranchBlock_0483 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 483 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 483 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 483 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7728 s
  · exact g32p_row31_cosetBranchStep_7729 s
  · exact g32p_row31_cosetBranchStep_7730 s
  · exact g32p_row31_cosetBranchStep_7731 s
  · exact g32p_row31_cosetBranchStep_7732 s
  · exact g32p_row31_cosetBranchStep_7733 s
  · exact g32p_row31_cosetBranchStep_7734 s
  · exact g32p_row31_cosetBranchStep_7735 s
  · exact g32p_row31_cosetBranchStep_7736 s
  · exact g32p_row31_cosetBranchStep_7737 s
  · exact g32p_row31_cosetBranchStep_7738 s
  · exact g32p_row31_cosetBranchStep_7739 s
  · exact g32p_row31_cosetBranchStep_7740 s
  · exact g32p_row31_cosetBranchStep_7741 s
  · exact g32p_row31_cosetBranchStep_7742 s
  · exact g32p_row31_cosetBranchStep_7743 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7744 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7744) = g32p_row31_cosetRepresentatives 7744 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7744 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7744) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7744))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7744)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7744 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7744) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7744))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7744)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7745 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7745) = g32p_row31_cosetRepresentatives 7745 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7745 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7745) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7745))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7745)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7745 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7745) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7745))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7745)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7746 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7746) = g32p_row31_cosetRepresentatives 7746 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7746 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7746) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7746))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7746)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7746 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7746) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7746))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7746)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7747 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7747) = g32p_row31_cosetRepresentatives 7747 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7747 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7747) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7747))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7747)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7747 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7747) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7747))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7747)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7748 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7748) = g32p_row31_cosetRepresentatives 7748 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7748 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7748) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7748))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7748)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7748 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7748) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7748))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7748)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7749 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7749) = g32p_row31_cosetRepresentatives 7749 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7749 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7749) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7749))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7749)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7749 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7749) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7749))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7749)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7750 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7750) = g32p_row31_cosetRepresentatives 7750 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7750 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7750) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7750))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7750)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7750 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7750) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7750))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7750)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7751 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7751) = g32p_row31_cosetRepresentatives 7751 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7751 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7751) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7751))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7751)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7751 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7751) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7751))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7751)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7752 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7752) = g32p_row31_cosetRepresentatives 7752 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7752 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7752) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7752))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7752)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7752 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7752) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7752))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7752)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7753 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7753) = g32p_row31_cosetRepresentatives 7753 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7753 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7753) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7753))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7753)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7753 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7753) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7753))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7753)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7754 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7754) = g32p_row31_cosetRepresentatives 7754 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7754 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7754) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7754))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7754)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7754 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7754) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7754))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7754)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7755 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7755) = g32p_row31_cosetRepresentatives 7755 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7755 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7755) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7755))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7755)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7755 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7755) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7755))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7755)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7756 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7756) = g32p_row31_cosetRepresentatives 7756 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7756 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7756) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7756))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7756)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7756 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7756) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7756))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7756)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7757 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7757) = g32p_row31_cosetRepresentatives 7757 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7757 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7757) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7757))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7757)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7757 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7757) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7757))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7757)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7758 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7758) = g32p_row31_cosetRepresentatives 7758 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7758 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7758) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7758))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7758)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7758 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7758) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7758))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7758)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7759 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7759) = g32p_row31_cosetRepresentatives 7759 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7759 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7759) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7759))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7759)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7759 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7759) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7759))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7759)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0484 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 484 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 484 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7744
  · exact g32p_row31_cosetWord_7745
  · exact g32p_row31_cosetWord_7746
  · exact g32p_row31_cosetWord_7747
  · exact g32p_row31_cosetWord_7748
  · exact g32p_row31_cosetWord_7749
  · exact g32p_row31_cosetWord_7750
  · exact g32p_row31_cosetWord_7751
  · exact g32p_row31_cosetWord_7752
  · exact g32p_row31_cosetWord_7753
  · exact g32p_row31_cosetWord_7754
  · exact g32p_row31_cosetWord_7755
  · exact g32p_row31_cosetWord_7756
  · exact g32p_row31_cosetWord_7757
  · exact g32p_row31_cosetWord_7758
  · exact g32p_row31_cosetWord_7759

theorem g32p_row31_cosetGeneratorBlock_0484 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 484 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 484 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 484 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7744 s
  · exact g32p_row31_cosetGeneratorStep_7745 s
  · exact g32p_row31_cosetGeneratorStep_7746 s
  · exact g32p_row31_cosetGeneratorStep_7747 s
  · exact g32p_row31_cosetGeneratorStep_7748 s
  · exact g32p_row31_cosetGeneratorStep_7749 s
  · exact g32p_row31_cosetGeneratorStep_7750 s
  · exact g32p_row31_cosetGeneratorStep_7751 s
  · exact g32p_row31_cosetGeneratorStep_7752 s
  · exact g32p_row31_cosetGeneratorStep_7753 s
  · exact g32p_row31_cosetGeneratorStep_7754 s
  · exact g32p_row31_cosetGeneratorStep_7755 s
  · exact g32p_row31_cosetGeneratorStep_7756 s
  · exact g32p_row31_cosetGeneratorStep_7757 s
  · exact g32p_row31_cosetGeneratorStep_7758 s
  · exact g32p_row31_cosetGeneratorStep_7759 s

theorem g32p_row31_cosetBranchBlock_0484 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 484 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 484 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 484 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7744 s
  · exact g32p_row31_cosetBranchStep_7745 s
  · exact g32p_row31_cosetBranchStep_7746 s
  · exact g32p_row31_cosetBranchStep_7747 s
  · exact g32p_row31_cosetBranchStep_7748 s
  · exact g32p_row31_cosetBranchStep_7749 s
  · exact g32p_row31_cosetBranchStep_7750 s
  · exact g32p_row31_cosetBranchStep_7751 s
  · exact g32p_row31_cosetBranchStep_7752 s
  · exact g32p_row31_cosetBranchStep_7753 s
  · exact g32p_row31_cosetBranchStep_7754 s
  · exact g32p_row31_cosetBranchStep_7755 s
  · exact g32p_row31_cosetBranchStep_7756 s
  · exact g32p_row31_cosetBranchStep_7757 s
  · exact g32p_row31_cosetBranchStep_7758 s
  · exact g32p_row31_cosetBranchStep_7759 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7760 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7760) = g32p_row31_cosetRepresentatives 7760 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7760 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7760) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7760))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7760)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7760 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7760) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7760))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7760)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7761 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7761) = g32p_row31_cosetRepresentatives 7761 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7761 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7761) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7761))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7761)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7761 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7761) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7761))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7761)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7762 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7762) = g32p_row31_cosetRepresentatives 7762 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7762 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7762) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7762))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7762)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7762 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7762) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7762))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7762)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7763 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7763) = g32p_row31_cosetRepresentatives 7763 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7763 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7763) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7763))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7763)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7763 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7763) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7763))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7763)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7764 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7764) = g32p_row31_cosetRepresentatives 7764 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7764 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7764) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7764))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7764)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7764 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7764) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7764))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7764)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7765 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7765) = g32p_row31_cosetRepresentatives 7765 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7765 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7765) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7765))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7765)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7765 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7765) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7765))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7765)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7766 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7766) = g32p_row31_cosetRepresentatives 7766 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7766 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7766) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7766))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7766)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7766 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7766) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7766))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7766)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7767 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7767) = g32p_row31_cosetRepresentatives 7767 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7767 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7767) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7767))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7767)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7767 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7767) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7767))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7767)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7768 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7768) = g32p_row31_cosetRepresentatives 7768 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7768 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7768) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7768))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7768)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7768 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7768) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7768))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7768)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7769 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7769) = g32p_row31_cosetRepresentatives 7769 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7769 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7769) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7769))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7769)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7769 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7769) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7769))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7769)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7770 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7770) = g32p_row31_cosetRepresentatives 7770 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7770 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7770) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7770))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7770)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7770 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7770) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7770))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7770)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7771 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7771) = g32p_row31_cosetRepresentatives 7771 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7771 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7771) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7771))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7771)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7771 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7771) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7771))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7771)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7772 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7772) = g32p_row31_cosetRepresentatives 7772 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7772 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7772) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7772))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7772)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7772 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7772) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7772))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7772)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7773 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7773) = g32p_row31_cosetRepresentatives 7773 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7773 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7773) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7773))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7773)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7773 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7773) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7773))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7773)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7774 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7774) = g32p_row31_cosetRepresentatives 7774 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7774 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7774) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7774))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7774)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7774 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7774) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7774))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7774)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7775 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7775) = g32p_row31_cosetRepresentatives 7775 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7775 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7775) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7775))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7775)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7775 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7775) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7775))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7775)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0485 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 485 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 485 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7760
  · exact g32p_row31_cosetWord_7761
  · exact g32p_row31_cosetWord_7762
  · exact g32p_row31_cosetWord_7763
  · exact g32p_row31_cosetWord_7764
  · exact g32p_row31_cosetWord_7765
  · exact g32p_row31_cosetWord_7766
  · exact g32p_row31_cosetWord_7767
  · exact g32p_row31_cosetWord_7768
  · exact g32p_row31_cosetWord_7769
  · exact g32p_row31_cosetWord_7770
  · exact g32p_row31_cosetWord_7771
  · exact g32p_row31_cosetWord_7772
  · exact g32p_row31_cosetWord_7773
  · exact g32p_row31_cosetWord_7774
  · exact g32p_row31_cosetWord_7775

theorem g32p_row31_cosetGeneratorBlock_0485 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 485 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 485 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 485 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7760 s
  · exact g32p_row31_cosetGeneratorStep_7761 s
  · exact g32p_row31_cosetGeneratorStep_7762 s
  · exact g32p_row31_cosetGeneratorStep_7763 s
  · exact g32p_row31_cosetGeneratorStep_7764 s
  · exact g32p_row31_cosetGeneratorStep_7765 s
  · exact g32p_row31_cosetGeneratorStep_7766 s
  · exact g32p_row31_cosetGeneratorStep_7767 s
  · exact g32p_row31_cosetGeneratorStep_7768 s
  · exact g32p_row31_cosetGeneratorStep_7769 s
  · exact g32p_row31_cosetGeneratorStep_7770 s
  · exact g32p_row31_cosetGeneratorStep_7771 s
  · exact g32p_row31_cosetGeneratorStep_7772 s
  · exact g32p_row31_cosetGeneratorStep_7773 s
  · exact g32p_row31_cosetGeneratorStep_7774 s
  · exact g32p_row31_cosetGeneratorStep_7775 s

theorem g32p_row31_cosetBranchBlock_0485 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 485 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 485 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 485 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7760 s
  · exact g32p_row31_cosetBranchStep_7761 s
  · exact g32p_row31_cosetBranchStep_7762 s
  · exact g32p_row31_cosetBranchStep_7763 s
  · exact g32p_row31_cosetBranchStep_7764 s
  · exact g32p_row31_cosetBranchStep_7765 s
  · exact g32p_row31_cosetBranchStep_7766 s
  · exact g32p_row31_cosetBranchStep_7767 s
  · exact g32p_row31_cosetBranchStep_7768 s
  · exact g32p_row31_cosetBranchStep_7769 s
  · exact g32p_row31_cosetBranchStep_7770 s
  · exact g32p_row31_cosetBranchStep_7771 s
  · exact g32p_row31_cosetBranchStep_7772 s
  · exact g32p_row31_cosetBranchStep_7773 s
  · exact g32p_row31_cosetBranchStep_7774 s
  · exact g32p_row31_cosetBranchStep_7775 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7776 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7776) = g32p_row31_cosetRepresentatives 7776 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7776 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7776) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7776))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7776)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7776 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7776) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7776))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7776)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7777 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7777) = g32p_row31_cosetRepresentatives 7777 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7777 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7777) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7777))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7777)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7777 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7777) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7777))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7777)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7778 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7778) = g32p_row31_cosetRepresentatives 7778 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7778 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7778) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7778))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7778)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7778 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7778) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7778))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7778)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7779 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7779) = g32p_row31_cosetRepresentatives 7779 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7779 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7779) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7779))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7779)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7779 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7779) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7779))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7779)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7780 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7780) = g32p_row31_cosetRepresentatives 7780 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7780 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7780) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7780))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7780)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7780 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7780) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7780))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7780)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7781 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7781) = g32p_row31_cosetRepresentatives 7781 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7781 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7781) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7781))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7781)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7781 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7781) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7781))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7781)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7782 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7782) = g32p_row31_cosetRepresentatives 7782 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7782 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7782) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7782))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7782)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7782 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7782) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7782))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7782)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7783 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7783) = g32p_row31_cosetRepresentatives 7783 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7783 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7783) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7783))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7783)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7783 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7783) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7783))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7783)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7784 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7784) = g32p_row31_cosetRepresentatives 7784 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7784 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7784) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7784))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7784)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7784 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7784) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7784))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7784)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7785 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7785) = g32p_row31_cosetRepresentatives 7785 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7785 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7785) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7785))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7785)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7785 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7785) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7785))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7785)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7786 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7786) = g32p_row31_cosetRepresentatives 7786 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7786 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7786) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7786))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7786)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7786 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7786) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7786))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7786)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7787 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7787) = g32p_row31_cosetRepresentatives 7787 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7787 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7787) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7787))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7787)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7787 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7787) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7787))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7787)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7788 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7788) = g32p_row31_cosetRepresentatives 7788 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7788 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7788) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7788))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7788)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7788 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7788) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7788))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7788)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7789 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7789) = g32p_row31_cosetRepresentatives 7789 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7789 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7789) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7789))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7789)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7789 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7789) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7789))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7789)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7790 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7790) = g32p_row31_cosetRepresentatives 7790 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7790 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7790) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7790))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7790)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7790 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7790) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7790))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7790)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7791 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7791) = g32p_row31_cosetRepresentatives 7791 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7791 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7791) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7791))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7791)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7791 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7791) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7791))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7791)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0486 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 486 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 486 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7776
  · exact g32p_row31_cosetWord_7777
  · exact g32p_row31_cosetWord_7778
  · exact g32p_row31_cosetWord_7779
  · exact g32p_row31_cosetWord_7780
  · exact g32p_row31_cosetWord_7781
  · exact g32p_row31_cosetWord_7782
  · exact g32p_row31_cosetWord_7783
  · exact g32p_row31_cosetWord_7784
  · exact g32p_row31_cosetWord_7785
  · exact g32p_row31_cosetWord_7786
  · exact g32p_row31_cosetWord_7787
  · exact g32p_row31_cosetWord_7788
  · exact g32p_row31_cosetWord_7789
  · exact g32p_row31_cosetWord_7790
  · exact g32p_row31_cosetWord_7791

theorem g32p_row31_cosetGeneratorBlock_0486 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 486 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 486 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 486 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7776 s
  · exact g32p_row31_cosetGeneratorStep_7777 s
  · exact g32p_row31_cosetGeneratorStep_7778 s
  · exact g32p_row31_cosetGeneratorStep_7779 s
  · exact g32p_row31_cosetGeneratorStep_7780 s
  · exact g32p_row31_cosetGeneratorStep_7781 s
  · exact g32p_row31_cosetGeneratorStep_7782 s
  · exact g32p_row31_cosetGeneratorStep_7783 s
  · exact g32p_row31_cosetGeneratorStep_7784 s
  · exact g32p_row31_cosetGeneratorStep_7785 s
  · exact g32p_row31_cosetGeneratorStep_7786 s
  · exact g32p_row31_cosetGeneratorStep_7787 s
  · exact g32p_row31_cosetGeneratorStep_7788 s
  · exact g32p_row31_cosetGeneratorStep_7789 s
  · exact g32p_row31_cosetGeneratorStep_7790 s
  · exact g32p_row31_cosetGeneratorStep_7791 s

theorem g32p_row31_cosetBranchBlock_0486 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 486 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 486 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 486 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7776 s
  · exact g32p_row31_cosetBranchStep_7777 s
  · exact g32p_row31_cosetBranchStep_7778 s
  · exact g32p_row31_cosetBranchStep_7779 s
  · exact g32p_row31_cosetBranchStep_7780 s
  · exact g32p_row31_cosetBranchStep_7781 s
  · exact g32p_row31_cosetBranchStep_7782 s
  · exact g32p_row31_cosetBranchStep_7783 s
  · exact g32p_row31_cosetBranchStep_7784 s
  · exact g32p_row31_cosetBranchStep_7785 s
  · exact g32p_row31_cosetBranchStep_7786 s
  · exact g32p_row31_cosetBranchStep_7787 s
  · exact g32p_row31_cosetBranchStep_7788 s
  · exact g32p_row31_cosetBranchStep_7789 s
  · exact g32p_row31_cosetBranchStep_7790 s
  · exact g32p_row31_cosetBranchStep_7791 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7792 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7792) = g32p_row31_cosetRepresentatives 7792 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7792 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7792) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7792))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7792)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7792 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7792) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7792))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7792)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7793 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7793) = g32p_row31_cosetRepresentatives 7793 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7793 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7793) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7793))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7793)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7793 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7793) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7793))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7793)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7794 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7794) = g32p_row31_cosetRepresentatives 7794 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7794 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7794) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7794))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7794)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7794 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7794) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7794))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7794)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7795 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7795) = g32p_row31_cosetRepresentatives 7795 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7795 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7795) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7795))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7795)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7795 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7795) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7795))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7795)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7796 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7796) = g32p_row31_cosetRepresentatives 7796 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7796 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7796) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7796))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7796)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7796 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7796) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7796))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7796)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7797 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7797) = g32p_row31_cosetRepresentatives 7797 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7797 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7797) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7797))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7797)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7797 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7797) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7797))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7797)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7798 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7798) = g32p_row31_cosetRepresentatives 7798 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7798 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7798) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7798))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7798)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7798 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7798) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7798))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7798)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7799 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7799) = g32p_row31_cosetRepresentatives 7799 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7799 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7799) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7799))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7799)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7799 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7799) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7799))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7799)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7800 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7800) = g32p_row31_cosetRepresentatives 7800 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7800 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7800) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7800))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7800)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7800 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7800) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7800))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7800)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7801 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7801) = g32p_row31_cosetRepresentatives 7801 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7801 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7801) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7801))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7801)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7801 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7801) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7801))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7801)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7802 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7802) = g32p_row31_cosetRepresentatives 7802 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7802 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7802) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7802))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7802)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7802 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7802) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7802))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7802)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7803 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7803) = g32p_row31_cosetRepresentatives 7803 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7803 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7803) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7803))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7803)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7803 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7803) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7803))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7803)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7804 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7804) = g32p_row31_cosetRepresentatives 7804 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7804 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7804) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7804))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7804)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7804 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7804) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7804))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7804)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7805 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7805) = g32p_row31_cosetRepresentatives 7805 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7805 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7805) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7805))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7805)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7805 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7805) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7805))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7805)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7806 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7806) = g32p_row31_cosetRepresentatives 7806 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7806 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7806) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7806))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7806)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7806 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7806) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7806))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7806)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7807 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7807) = g32p_row31_cosetRepresentatives 7807 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7807 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7807) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7807))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7807)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7807 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7807) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7807))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7807)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0487 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 487 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 487 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7792
  · exact g32p_row31_cosetWord_7793
  · exact g32p_row31_cosetWord_7794
  · exact g32p_row31_cosetWord_7795
  · exact g32p_row31_cosetWord_7796
  · exact g32p_row31_cosetWord_7797
  · exact g32p_row31_cosetWord_7798
  · exact g32p_row31_cosetWord_7799
  · exact g32p_row31_cosetWord_7800
  · exact g32p_row31_cosetWord_7801
  · exact g32p_row31_cosetWord_7802
  · exact g32p_row31_cosetWord_7803
  · exact g32p_row31_cosetWord_7804
  · exact g32p_row31_cosetWord_7805
  · exact g32p_row31_cosetWord_7806
  · exact g32p_row31_cosetWord_7807

theorem g32p_row31_cosetGeneratorBlock_0487 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 487 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 487 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 487 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7792 s
  · exact g32p_row31_cosetGeneratorStep_7793 s
  · exact g32p_row31_cosetGeneratorStep_7794 s
  · exact g32p_row31_cosetGeneratorStep_7795 s
  · exact g32p_row31_cosetGeneratorStep_7796 s
  · exact g32p_row31_cosetGeneratorStep_7797 s
  · exact g32p_row31_cosetGeneratorStep_7798 s
  · exact g32p_row31_cosetGeneratorStep_7799 s
  · exact g32p_row31_cosetGeneratorStep_7800 s
  · exact g32p_row31_cosetGeneratorStep_7801 s
  · exact g32p_row31_cosetGeneratorStep_7802 s
  · exact g32p_row31_cosetGeneratorStep_7803 s
  · exact g32p_row31_cosetGeneratorStep_7804 s
  · exact g32p_row31_cosetGeneratorStep_7805 s
  · exact g32p_row31_cosetGeneratorStep_7806 s
  · exact g32p_row31_cosetGeneratorStep_7807 s

theorem g32p_row31_cosetBranchBlock_0487 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 487 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 487 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 487 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7792 s
  · exact g32p_row31_cosetBranchStep_7793 s
  · exact g32p_row31_cosetBranchStep_7794 s
  · exact g32p_row31_cosetBranchStep_7795 s
  · exact g32p_row31_cosetBranchStep_7796 s
  · exact g32p_row31_cosetBranchStep_7797 s
  · exact g32p_row31_cosetBranchStep_7798 s
  · exact g32p_row31_cosetBranchStep_7799 s
  · exact g32p_row31_cosetBranchStep_7800 s
  · exact g32p_row31_cosetBranchStep_7801 s
  · exact g32p_row31_cosetBranchStep_7802 s
  · exact g32p_row31_cosetBranchStep_7803 s
  · exact g32p_row31_cosetBranchStep_7804 s
  · exact g32p_row31_cosetBranchStep_7805 s
  · exact g32p_row31_cosetBranchStep_7806 s
  · exact g32p_row31_cosetBranchStep_7807 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7808 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7808) = g32p_row31_cosetRepresentatives 7808 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7808 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7808) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7808))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7808)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7808 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7808) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7808))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7808)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7809 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7809) = g32p_row31_cosetRepresentatives 7809 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7809 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7809) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7809))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7809)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7809 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7809) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7809))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7809)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7810 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7810) = g32p_row31_cosetRepresentatives 7810 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7810 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7810) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7810))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7810)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7810 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7810) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7810))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7810)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7811 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7811) = g32p_row31_cosetRepresentatives 7811 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7811 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7811) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7811))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7811)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7811 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7811) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7811))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7811)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7812 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7812) = g32p_row31_cosetRepresentatives 7812 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7812 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7812) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7812))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7812)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7812 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7812) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7812))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7812)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7813 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7813) = g32p_row31_cosetRepresentatives 7813 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7813 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7813) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7813))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7813)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7813 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7813) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7813))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7813)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7814 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7814) = g32p_row31_cosetRepresentatives 7814 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7814 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7814) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7814))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7814)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7814 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7814) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7814))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7814)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7815 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7815) = g32p_row31_cosetRepresentatives 7815 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7815 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7815) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7815))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7815)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7815 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7815) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7815))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7815)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7816 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7816) = g32p_row31_cosetRepresentatives 7816 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7816 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7816) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7816))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7816)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7816 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7816) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7816))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7816)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7817 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7817) = g32p_row31_cosetRepresentatives 7817 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7817 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7817) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7817))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7817)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7817 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7817) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7817))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7817)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7818 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7818) = g32p_row31_cosetRepresentatives 7818 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7818 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7818) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7818))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7818)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7818 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7818) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7818))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7818)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7819 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7819) = g32p_row31_cosetRepresentatives 7819 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7819 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7819) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7819))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7819)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7819 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7819) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7819))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7819)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7820 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7820) = g32p_row31_cosetRepresentatives 7820 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7820 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7820) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7820))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7820)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7820 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7820) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7820))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7820)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7821 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7821) = g32p_row31_cosetRepresentatives 7821 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7821 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7821) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7821))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7821)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7821 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7821) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7821))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7821)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7822 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7822) = g32p_row31_cosetRepresentatives 7822 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7822 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7822) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7822))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7822)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7822 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7822) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7822))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7822)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7823 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7823) = g32p_row31_cosetRepresentatives 7823 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7823 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7823) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7823))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7823)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7823 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7823) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7823))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7823)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0488 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 488 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 488 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7808
  · exact g32p_row31_cosetWord_7809
  · exact g32p_row31_cosetWord_7810
  · exact g32p_row31_cosetWord_7811
  · exact g32p_row31_cosetWord_7812
  · exact g32p_row31_cosetWord_7813
  · exact g32p_row31_cosetWord_7814
  · exact g32p_row31_cosetWord_7815
  · exact g32p_row31_cosetWord_7816
  · exact g32p_row31_cosetWord_7817
  · exact g32p_row31_cosetWord_7818
  · exact g32p_row31_cosetWord_7819
  · exact g32p_row31_cosetWord_7820
  · exact g32p_row31_cosetWord_7821
  · exact g32p_row31_cosetWord_7822
  · exact g32p_row31_cosetWord_7823

theorem g32p_row31_cosetGeneratorBlock_0488 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 488 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 488 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 488 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7808 s
  · exact g32p_row31_cosetGeneratorStep_7809 s
  · exact g32p_row31_cosetGeneratorStep_7810 s
  · exact g32p_row31_cosetGeneratorStep_7811 s
  · exact g32p_row31_cosetGeneratorStep_7812 s
  · exact g32p_row31_cosetGeneratorStep_7813 s
  · exact g32p_row31_cosetGeneratorStep_7814 s
  · exact g32p_row31_cosetGeneratorStep_7815 s
  · exact g32p_row31_cosetGeneratorStep_7816 s
  · exact g32p_row31_cosetGeneratorStep_7817 s
  · exact g32p_row31_cosetGeneratorStep_7818 s
  · exact g32p_row31_cosetGeneratorStep_7819 s
  · exact g32p_row31_cosetGeneratorStep_7820 s
  · exact g32p_row31_cosetGeneratorStep_7821 s
  · exact g32p_row31_cosetGeneratorStep_7822 s
  · exact g32p_row31_cosetGeneratorStep_7823 s

theorem g32p_row31_cosetBranchBlock_0488 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 488 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 488 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 488 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7808 s
  · exact g32p_row31_cosetBranchStep_7809 s
  · exact g32p_row31_cosetBranchStep_7810 s
  · exact g32p_row31_cosetBranchStep_7811 s
  · exact g32p_row31_cosetBranchStep_7812 s
  · exact g32p_row31_cosetBranchStep_7813 s
  · exact g32p_row31_cosetBranchStep_7814 s
  · exact g32p_row31_cosetBranchStep_7815 s
  · exact g32p_row31_cosetBranchStep_7816 s
  · exact g32p_row31_cosetBranchStep_7817 s
  · exact g32p_row31_cosetBranchStep_7818 s
  · exact g32p_row31_cosetBranchStep_7819 s
  · exact g32p_row31_cosetBranchStep_7820 s
  · exact g32p_row31_cosetBranchStep_7821 s
  · exact g32p_row31_cosetBranchStep_7822 s
  · exact g32p_row31_cosetBranchStep_7823 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7824 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7824) = g32p_row31_cosetRepresentatives 7824 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7824 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7824) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7824))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7824)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7824 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7824) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7824))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7824)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7825 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7825) = g32p_row31_cosetRepresentatives 7825 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7825 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7825) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7825))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7825)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7825 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7825) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7825))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7825)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7826 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7826) = g32p_row31_cosetRepresentatives 7826 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7826 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7826) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7826))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7826)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7826 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7826) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7826))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7826)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7827 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7827) = g32p_row31_cosetRepresentatives 7827 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7827 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7827) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7827))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7827)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7827 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7827) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7827))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7827)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7828 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7828) = g32p_row31_cosetRepresentatives 7828 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7828 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7828) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7828))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7828)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7828 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7828) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7828))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7828)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7829 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7829) = g32p_row31_cosetRepresentatives 7829 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7829 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7829) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7829))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7829)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7829 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7829) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7829))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7829)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7830 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7830) = g32p_row31_cosetRepresentatives 7830 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7830 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7830) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7830))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7830)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7830 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7830) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7830))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7830)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7831 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7831) = g32p_row31_cosetRepresentatives 7831 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7831 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7831) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7831))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7831)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7831 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7831) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7831))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7831)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7832 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7832) = g32p_row31_cosetRepresentatives 7832 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7832 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7832) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7832))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7832)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7832 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7832) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7832))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7832)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7833 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7833) = g32p_row31_cosetRepresentatives 7833 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7833 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7833) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7833))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7833)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7833 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7833) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7833))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7833)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7834 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7834) = g32p_row31_cosetRepresentatives 7834 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7834 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7834) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7834))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7834)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7834 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7834) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7834))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7834)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7835 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7835) = g32p_row31_cosetRepresentatives 7835 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7835 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7835) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7835))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7835)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7835 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7835) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7835))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7835)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7836 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7836) = g32p_row31_cosetRepresentatives 7836 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7836 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7836) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7836))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7836)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7836 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7836) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7836))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7836)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7837 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7837) = g32p_row31_cosetRepresentatives 7837 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7837 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7837) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7837))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7837)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7837 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7837) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7837))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7837)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7838 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7838) = g32p_row31_cosetRepresentatives 7838 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7838 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7838) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7838))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7838)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7838 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7838) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7838))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7838)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7839 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7839) = g32p_row31_cosetRepresentatives 7839 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7839 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7839) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7839))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7839)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7839 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7839) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7839))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7839)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0489 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 489 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 489 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7824
  · exact g32p_row31_cosetWord_7825
  · exact g32p_row31_cosetWord_7826
  · exact g32p_row31_cosetWord_7827
  · exact g32p_row31_cosetWord_7828
  · exact g32p_row31_cosetWord_7829
  · exact g32p_row31_cosetWord_7830
  · exact g32p_row31_cosetWord_7831
  · exact g32p_row31_cosetWord_7832
  · exact g32p_row31_cosetWord_7833
  · exact g32p_row31_cosetWord_7834
  · exact g32p_row31_cosetWord_7835
  · exact g32p_row31_cosetWord_7836
  · exact g32p_row31_cosetWord_7837
  · exact g32p_row31_cosetWord_7838
  · exact g32p_row31_cosetWord_7839

theorem g32p_row31_cosetGeneratorBlock_0489 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 489 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 489 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 489 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7824 s
  · exact g32p_row31_cosetGeneratorStep_7825 s
  · exact g32p_row31_cosetGeneratorStep_7826 s
  · exact g32p_row31_cosetGeneratorStep_7827 s
  · exact g32p_row31_cosetGeneratorStep_7828 s
  · exact g32p_row31_cosetGeneratorStep_7829 s
  · exact g32p_row31_cosetGeneratorStep_7830 s
  · exact g32p_row31_cosetGeneratorStep_7831 s
  · exact g32p_row31_cosetGeneratorStep_7832 s
  · exact g32p_row31_cosetGeneratorStep_7833 s
  · exact g32p_row31_cosetGeneratorStep_7834 s
  · exact g32p_row31_cosetGeneratorStep_7835 s
  · exact g32p_row31_cosetGeneratorStep_7836 s
  · exact g32p_row31_cosetGeneratorStep_7837 s
  · exact g32p_row31_cosetGeneratorStep_7838 s
  · exact g32p_row31_cosetGeneratorStep_7839 s

theorem g32p_row31_cosetBranchBlock_0489 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 489 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 489 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 489 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7824 s
  · exact g32p_row31_cosetBranchStep_7825 s
  · exact g32p_row31_cosetBranchStep_7826 s
  · exact g32p_row31_cosetBranchStep_7827 s
  · exact g32p_row31_cosetBranchStep_7828 s
  · exact g32p_row31_cosetBranchStep_7829 s
  · exact g32p_row31_cosetBranchStep_7830 s
  · exact g32p_row31_cosetBranchStep_7831 s
  · exact g32p_row31_cosetBranchStep_7832 s
  · exact g32p_row31_cosetBranchStep_7833 s
  · exact g32p_row31_cosetBranchStep_7834 s
  · exact g32p_row31_cosetBranchStep_7835 s
  · exact g32p_row31_cosetBranchStep_7836 s
  · exact g32p_row31_cosetBranchStep_7837 s
  · exact g32p_row31_cosetBranchStep_7838 s
  · exact g32p_row31_cosetBranchStep_7839 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7840 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7840) = g32p_row31_cosetRepresentatives 7840 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7840 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7840) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7840))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7840)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7840 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7840) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7840))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7840)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7841 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7841) = g32p_row31_cosetRepresentatives 7841 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7841 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7841) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7841))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7841)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7841 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7841) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7841))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7841)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7842 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7842) = g32p_row31_cosetRepresentatives 7842 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7842 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7842) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7842))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7842)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7842 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7842) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7842))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7842)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7843 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7843) = g32p_row31_cosetRepresentatives 7843 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7843 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7843) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7843))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7843)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7843 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7843) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7843))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7843)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7844 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7844) = g32p_row31_cosetRepresentatives 7844 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7844 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7844) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7844))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7844)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7844 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7844) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7844))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7844)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7845 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7845) = g32p_row31_cosetRepresentatives 7845 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7845 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7845) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7845))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7845)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7845 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7845) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7845))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7845)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7846 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7846) = g32p_row31_cosetRepresentatives 7846 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7846 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7846) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7846))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7846)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7846 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7846) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7846))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7846)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7847 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7847) = g32p_row31_cosetRepresentatives 7847 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7847 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7847) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7847))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7847)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7847 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7847) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7847))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7847)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7848 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7848) = g32p_row31_cosetRepresentatives 7848 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7848 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7848) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7848))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7848)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7848 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7848) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7848))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7848)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7849 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7849) = g32p_row31_cosetRepresentatives 7849 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7849 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7849) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7849))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7849)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7849 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7849) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7849))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7849)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7850 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7850) = g32p_row31_cosetRepresentatives 7850 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7850 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7850) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7850))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7850)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7850 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7850) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7850))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7850)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7851 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7851) = g32p_row31_cosetRepresentatives 7851 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7851 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7851) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7851))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7851)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7851 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7851) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7851))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7851)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7852 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7852) = g32p_row31_cosetRepresentatives 7852 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7852 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7852) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7852))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7852)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7852 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7852) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7852))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7852)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7853 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7853) = g32p_row31_cosetRepresentatives 7853 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7853 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7853) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7853))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7853)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7853 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7853) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7853))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7853)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7854 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7854) = g32p_row31_cosetRepresentatives 7854 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7854 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7854) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7854))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7854)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7854 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7854) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7854))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7854)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7855 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7855) = g32p_row31_cosetRepresentatives 7855 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7855 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7855) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7855))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7855)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7855 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7855) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7855))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7855)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0490 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 490 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 490 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7840
  · exact g32p_row31_cosetWord_7841
  · exact g32p_row31_cosetWord_7842
  · exact g32p_row31_cosetWord_7843
  · exact g32p_row31_cosetWord_7844
  · exact g32p_row31_cosetWord_7845
  · exact g32p_row31_cosetWord_7846
  · exact g32p_row31_cosetWord_7847
  · exact g32p_row31_cosetWord_7848
  · exact g32p_row31_cosetWord_7849
  · exact g32p_row31_cosetWord_7850
  · exact g32p_row31_cosetWord_7851
  · exact g32p_row31_cosetWord_7852
  · exact g32p_row31_cosetWord_7853
  · exact g32p_row31_cosetWord_7854
  · exact g32p_row31_cosetWord_7855

theorem g32p_row31_cosetGeneratorBlock_0490 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 490 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 490 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 490 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7840 s
  · exact g32p_row31_cosetGeneratorStep_7841 s
  · exact g32p_row31_cosetGeneratorStep_7842 s
  · exact g32p_row31_cosetGeneratorStep_7843 s
  · exact g32p_row31_cosetGeneratorStep_7844 s
  · exact g32p_row31_cosetGeneratorStep_7845 s
  · exact g32p_row31_cosetGeneratorStep_7846 s
  · exact g32p_row31_cosetGeneratorStep_7847 s
  · exact g32p_row31_cosetGeneratorStep_7848 s
  · exact g32p_row31_cosetGeneratorStep_7849 s
  · exact g32p_row31_cosetGeneratorStep_7850 s
  · exact g32p_row31_cosetGeneratorStep_7851 s
  · exact g32p_row31_cosetGeneratorStep_7852 s
  · exact g32p_row31_cosetGeneratorStep_7853 s
  · exact g32p_row31_cosetGeneratorStep_7854 s
  · exact g32p_row31_cosetGeneratorStep_7855 s

theorem g32p_row31_cosetBranchBlock_0490 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 490 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 490 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 490 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7840 s
  · exact g32p_row31_cosetBranchStep_7841 s
  · exact g32p_row31_cosetBranchStep_7842 s
  · exact g32p_row31_cosetBranchStep_7843 s
  · exact g32p_row31_cosetBranchStep_7844 s
  · exact g32p_row31_cosetBranchStep_7845 s
  · exact g32p_row31_cosetBranchStep_7846 s
  · exact g32p_row31_cosetBranchStep_7847 s
  · exact g32p_row31_cosetBranchStep_7848 s
  · exact g32p_row31_cosetBranchStep_7849 s
  · exact g32p_row31_cosetBranchStep_7850 s
  · exact g32p_row31_cosetBranchStep_7851 s
  · exact g32p_row31_cosetBranchStep_7852 s
  · exact g32p_row31_cosetBranchStep_7853 s
  · exact g32p_row31_cosetBranchStep_7854 s
  · exact g32p_row31_cosetBranchStep_7855 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7856 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7856) = g32p_row31_cosetRepresentatives 7856 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7856 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7856) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7856))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7856)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7856 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7856) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7856))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7856)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7857 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7857) = g32p_row31_cosetRepresentatives 7857 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7857 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7857) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7857))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7857)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7857 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7857) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7857))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7857)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7858 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7858) = g32p_row31_cosetRepresentatives 7858 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7858 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7858) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7858))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7858)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7858 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7858) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7858))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7858)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7859 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7859) = g32p_row31_cosetRepresentatives 7859 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7859 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7859) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7859))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7859)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7859 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7859) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7859))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7859)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7860 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7860) = g32p_row31_cosetRepresentatives 7860 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7860 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7860) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7860))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7860)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7860 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7860) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7860))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7860)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7861 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7861) = g32p_row31_cosetRepresentatives 7861 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7861 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7861) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7861))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7861)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7861 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7861) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7861))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7861)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7862 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7862) = g32p_row31_cosetRepresentatives 7862 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7862 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7862) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7862))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7862)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7862 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7862) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7862))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7862)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7863 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7863) = g32p_row31_cosetRepresentatives 7863 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7863 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7863) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7863))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7863)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7863 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7863) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7863))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7863)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7864 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7864) = g32p_row31_cosetRepresentatives 7864 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7864 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7864) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7864))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7864)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7864 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7864) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7864))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7864)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7865 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7865) = g32p_row31_cosetRepresentatives 7865 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7865 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7865) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7865))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7865)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7865 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7865) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7865))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7865)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7866 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7866) = g32p_row31_cosetRepresentatives 7866 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7866 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7866) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7866))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7866)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7866 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7866) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7866))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7866)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7867 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7867) = g32p_row31_cosetRepresentatives 7867 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7867 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7867) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7867))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7867)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7867 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7867) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7867))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7867)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7868 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7868) = g32p_row31_cosetRepresentatives 7868 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7868 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7868) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7868))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7868)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7868 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7868) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7868))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7868)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7869 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7869) = g32p_row31_cosetRepresentatives 7869 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7869 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7869) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7869))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7869)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7869 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7869) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7869))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7869)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7870 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7870) = g32p_row31_cosetRepresentatives 7870 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7870 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7870) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7870))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7870)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7870 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7870) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7870))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7870)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7871 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7871) = g32p_row31_cosetRepresentatives 7871 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7871 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7871) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7871))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7871)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7871 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7871) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7871))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7871)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0491 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 491 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 491 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7856
  · exact g32p_row31_cosetWord_7857
  · exact g32p_row31_cosetWord_7858
  · exact g32p_row31_cosetWord_7859
  · exact g32p_row31_cosetWord_7860
  · exact g32p_row31_cosetWord_7861
  · exact g32p_row31_cosetWord_7862
  · exact g32p_row31_cosetWord_7863
  · exact g32p_row31_cosetWord_7864
  · exact g32p_row31_cosetWord_7865
  · exact g32p_row31_cosetWord_7866
  · exact g32p_row31_cosetWord_7867
  · exact g32p_row31_cosetWord_7868
  · exact g32p_row31_cosetWord_7869
  · exact g32p_row31_cosetWord_7870
  · exact g32p_row31_cosetWord_7871

theorem g32p_row31_cosetGeneratorBlock_0491 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 491 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 491 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 491 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7856 s
  · exact g32p_row31_cosetGeneratorStep_7857 s
  · exact g32p_row31_cosetGeneratorStep_7858 s
  · exact g32p_row31_cosetGeneratorStep_7859 s
  · exact g32p_row31_cosetGeneratorStep_7860 s
  · exact g32p_row31_cosetGeneratorStep_7861 s
  · exact g32p_row31_cosetGeneratorStep_7862 s
  · exact g32p_row31_cosetGeneratorStep_7863 s
  · exact g32p_row31_cosetGeneratorStep_7864 s
  · exact g32p_row31_cosetGeneratorStep_7865 s
  · exact g32p_row31_cosetGeneratorStep_7866 s
  · exact g32p_row31_cosetGeneratorStep_7867 s
  · exact g32p_row31_cosetGeneratorStep_7868 s
  · exact g32p_row31_cosetGeneratorStep_7869 s
  · exact g32p_row31_cosetGeneratorStep_7870 s
  · exact g32p_row31_cosetGeneratorStep_7871 s

theorem g32p_row31_cosetBranchBlock_0491 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 491 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 491 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 491 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7856 s
  · exact g32p_row31_cosetBranchStep_7857 s
  · exact g32p_row31_cosetBranchStep_7858 s
  · exact g32p_row31_cosetBranchStep_7859 s
  · exact g32p_row31_cosetBranchStep_7860 s
  · exact g32p_row31_cosetBranchStep_7861 s
  · exact g32p_row31_cosetBranchStep_7862 s
  · exact g32p_row31_cosetBranchStep_7863 s
  · exact g32p_row31_cosetBranchStep_7864 s
  · exact g32p_row31_cosetBranchStep_7865 s
  · exact g32p_row31_cosetBranchStep_7866 s
  · exact g32p_row31_cosetBranchStep_7867 s
  · exact g32p_row31_cosetBranchStep_7868 s
  · exact g32p_row31_cosetBranchStep_7869 s
  · exact g32p_row31_cosetBranchStep_7870 s
  · exact g32p_row31_cosetBranchStep_7871 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7872 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7872) = g32p_row31_cosetRepresentatives 7872 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7872 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7872) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7872))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7872)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7872 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7872) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7872))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7872)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7873 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7873) = g32p_row31_cosetRepresentatives 7873 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7873 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7873) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7873))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7873)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7873 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7873) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7873))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7873)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7874 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7874) = g32p_row31_cosetRepresentatives 7874 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7874 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7874) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7874))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7874)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7874 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7874) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7874))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7874)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7875 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7875) = g32p_row31_cosetRepresentatives 7875 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7875 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7875) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7875))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7875)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7875 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7875) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7875))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7875)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7876 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7876) = g32p_row31_cosetRepresentatives 7876 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7876 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7876) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7876))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7876)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7876 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7876) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7876))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7876)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7877 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7877) = g32p_row31_cosetRepresentatives 7877 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7877 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7877) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7877))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7877)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7877 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7877) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7877))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7877)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7878 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7878) = g32p_row31_cosetRepresentatives 7878 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7878 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7878) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7878))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7878)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7878 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7878) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7878))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7878)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7879 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7879) = g32p_row31_cosetRepresentatives 7879 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7879 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7879) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7879))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7879)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7879 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7879) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7879))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7879)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7880 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7880) = g32p_row31_cosetRepresentatives 7880 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7880 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7880) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7880))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7880)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7880 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7880) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7880))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7880)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7881 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7881) = g32p_row31_cosetRepresentatives 7881 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7881 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7881) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7881))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7881)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7881 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7881) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7881))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7881)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7882 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7882) = g32p_row31_cosetRepresentatives 7882 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7882 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7882) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7882))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7882)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7882 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7882) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7882))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7882)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7883 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7883) = g32p_row31_cosetRepresentatives 7883 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7883 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7883) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7883))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7883)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7883 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7883) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7883))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7883)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7884 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7884) = g32p_row31_cosetRepresentatives 7884 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7884 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7884) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7884))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7884)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7884 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7884) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7884))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7884)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7885 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7885) = g32p_row31_cosetRepresentatives 7885 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7885 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7885) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7885))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7885)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7885 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7885) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7885))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7885)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7886 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7886) = g32p_row31_cosetRepresentatives 7886 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7886 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7886) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7886))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7886)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7886 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7886) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7886))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7886)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7887 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7887) = g32p_row31_cosetRepresentatives 7887 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7887 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7887) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7887))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7887)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7887 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7887) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7887))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7887)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0492 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 492 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 492 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7872
  · exact g32p_row31_cosetWord_7873
  · exact g32p_row31_cosetWord_7874
  · exact g32p_row31_cosetWord_7875
  · exact g32p_row31_cosetWord_7876
  · exact g32p_row31_cosetWord_7877
  · exact g32p_row31_cosetWord_7878
  · exact g32p_row31_cosetWord_7879
  · exact g32p_row31_cosetWord_7880
  · exact g32p_row31_cosetWord_7881
  · exact g32p_row31_cosetWord_7882
  · exact g32p_row31_cosetWord_7883
  · exact g32p_row31_cosetWord_7884
  · exact g32p_row31_cosetWord_7885
  · exact g32p_row31_cosetWord_7886
  · exact g32p_row31_cosetWord_7887

theorem g32p_row31_cosetGeneratorBlock_0492 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 492 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 492 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 492 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7872 s
  · exact g32p_row31_cosetGeneratorStep_7873 s
  · exact g32p_row31_cosetGeneratorStep_7874 s
  · exact g32p_row31_cosetGeneratorStep_7875 s
  · exact g32p_row31_cosetGeneratorStep_7876 s
  · exact g32p_row31_cosetGeneratorStep_7877 s
  · exact g32p_row31_cosetGeneratorStep_7878 s
  · exact g32p_row31_cosetGeneratorStep_7879 s
  · exact g32p_row31_cosetGeneratorStep_7880 s
  · exact g32p_row31_cosetGeneratorStep_7881 s
  · exact g32p_row31_cosetGeneratorStep_7882 s
  · exact g32p_row31_cosetGeneratorStep_7883 s
  · exact g32p_row31_cosetGeneratorStep_7884 s
  · exact g32p_row31_cosetGeneratorStep_7885 s
  · exact g32p_row31_cosetGeneratorStep_7886 s
  · exact g32p_row31_cosetGeneratorStep_7887 s

theorem g32p_row31_cosetBranchBlock_0492 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 492 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 492 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 492 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7872 s
  · exact g32p_row31_cosetBranchStep_7873 s
  · exact g32p_row31_cosetBranchStep_7874 s
  · exact g32p_row31_cosetBranchStep_7875 s
  · exact g32p_row31_cosetBranchStep_7876 s
  · exact g32p_row31_cosetBranchStep_7877 s
  · exact g32p_row31_cosetBranchStep_7878 s
  · exact g32p_row31_cosetBranchStep_7879 s
  · exact g32p_row31_cosetBranchStep_7880 s
  · exact g32p_row31_cosetBranchStep_7881 s
  · exact g32p_row31_cosetBranchStep_7882 s
  · exact g32p_row31_cosetBranchStep_7883 s
  · exact g32p_row31_cosetBranchStep_7884 s
  · exact g32p_row31_cosetBranchStep_7885 s
  · exact g32p_row31_cosetBranchStep_7886 s
  · exact g32p_row31_cosetBranchStep_7887 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7888 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7888) = g32p_row31_cosetRepresentatives 7888 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7888 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7888) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7888))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7888)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7888 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7888) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7888))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7888)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7889 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7889) = g32p_row31_cosetRepresentatives 7889 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7889 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7889) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7889))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7889)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7889 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7889) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7889))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7889)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7890 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7890) = g32p_row31_cosetRepresentatives 7890 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7890 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7890) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7890))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7890)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7890 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7890) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7890))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7890)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7891 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7891) = g32p_row31_cosetRepresentatives 7891 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7891 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7891) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7891))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7891)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7891 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7891) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7891))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7891)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7892 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7892) = g32p_row31_cosetRepresentatives 7892 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7892 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7892) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7892))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7892)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7892 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7892) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7892))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7892)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7893 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7893) = g32p_row31_cosetRepresentatives 7893 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7893 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7893) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7893))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7893)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7893 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7893) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7893))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7893)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7894 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7894) = g32p_row31_cosetRepresentatives 7894 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7894 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7894) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7894))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7894)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7894 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7894) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7894))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7894)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7895 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7895) = g32p_row31_cosetRepresentatives 7895 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7895 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7895) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7895))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7895)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7895 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7895) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7895))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7895)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7896 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7896) = g32p_row31_cosetRepresentatives 7896 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7896 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7896) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7896))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7896)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7896 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7896) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7896))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7896)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7897 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7897) = g32p_row31_cosetRepresentatives 7897 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7897 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7897) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7897))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7897)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7897 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7897) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7897))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7897)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7898 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7898) = g32p_row31_cosetRepresentatives 7898 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7898 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7898) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7898))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7898)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7898 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7898) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7898))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7898)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7899 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7899) = g32p_row31_cosetRepresentatives 7899 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7899 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7899) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7899))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7899)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7899 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7899) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7899))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7899)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7900 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7900) = g32p_row31_cosetRepresentatives 7900 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7900 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7900) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7900))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7900)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7900 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7900) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7900))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7900)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7901 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7901) = g32p_row31_cosetRepresentatives 7901 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7901 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7901) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7901))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7901)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7901 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7901) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7901))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7901)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7902 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7902) = g32p_row31_cosetRepresentatives 7902 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7902 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7902) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7902))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7902)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7902 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7902) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7902))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7902)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7903 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7903) = g32p_row31_cosetRepresentatives 7903 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7903 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7903) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7903))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7903)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7903 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7903) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7903))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7903)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0493 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 493 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 493 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7888
  · exact g32p_row31_cosetWord_7889
  · exact g32p_row31_cosetWord_7890
  · exact g32p_row31_cosetWord_7891
  · exact g32p_row31_cosetWord_7892
  · exact g32p_row31_cosetWord_7893
  · exact g32p_row31_cosetWord_7894
  · exact g32p_row31_cosetWord_7895
  · exact g32p_row31_cosetWord_7896
  · exact g32p_row31_cosetWord_7897
  · exact g32p_row31_cosetWord_7898
  · exact g32p_row31_cosetWord_7899
  · exact g32p_row31_cosetWord_7900
  · exact g32p_row31_cosetWord_7901
  · exact g32p_row31_cosetWord_7902
  · exact g32p_row31_cosetWord_7903

theorem g32p_row31_cosetGeneratorBlock_0493 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 493 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 493 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 493 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7888 s
  · exact g32p_row31_cosetGeneratorStep_7889 s
  · exact g32p_row31_cosetGeneratorStep_7890 s
  · exact g32p_row31_cosetGeneratorStep_7891 s
  · exact g32p_row31_cosetGeneratorStep_7892 s
  · exact g32p_row31_cosetGeneratorStep_7893 s
  · exact g32p_row31_cosetGeneratorStep_7894 s
  · exact g32p_row31_cosetGeneratorStep_7895 s
  · exact g32p_row31_cosetGeneratorStep_7896 s
  · exact g32p_row31_cosetGeneratorStep_7897 s
  · exact g32p_row31_cosetGeneratorStep_7898 s
  · exact g32p_row31_cosetGeneratorStep_7899 s
  · exact g32p_row31_cosetGeneratorStep_7900 s
  · exact g32p_row31_cosetGeneratorStep_7901 s
  · exact g32p_row31_cosetGeneratorStep_7902 s
  · exact g32p_row31_cosetGeneratorStep_7903 s

theorem g32p_row31_cosetBranchBlock_0493 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 493 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 493 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 493 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7888 s
  · exact g32p_row31_cosetBranchStep_7889 s
  · exact g32p_row31_cosetBranchStep_7890 s
  · exact g32p_row31_cosetBranchStep_7891 s
  · exact g32p_row31_cosetBranchStep_7892 s
  · exact g32p_row31_cosetBranchStep_7893 s
  · exact g32p_row31_cosetBranchStep_7894 s
  · exact g32p_row31_cosetBranchStep_7895 s
  · exact g32p_row31_cosetBranchStep_7896 s
  · exact g32p_row31_cosetBranchStep_7897 s
  · exact g32p_row31_cosetBranchStep_7898 s
  · exact g32p_row31_cosetBranchStep_7899 s
  · exact g32p_row31_cosetBranchStep_7900 s
  · exact g32p_row31_cosetBranchStep_7901 s
  · exact g32p_row31_cosetBranchStep_7902 s
  · exact g32p_row31_cosetBranchStep_7903 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7904 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7904) = g32p_row31_cosetRepresentatives 7904 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7904 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7904) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7904))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7904)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7904 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7904) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7904))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7904)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7905 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7905) = g32p_row31_cosetRepresentatives 7905 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7905 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7905) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7905))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7905)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7905 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7905) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7905))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7905)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7906 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7906) = g32p_row31_cosetRepresentatives 7906 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7906 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7906) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7906))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7906)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7906 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7906) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7906))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7906)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7907 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7907) = g32p_row31_cosetRepresentatives 7907 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7907 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7907) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7907))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7907)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7907 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7907) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7907))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7907)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7908 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7908) = g32p_row31_cosetRepresentatives 7908 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7908 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7908) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7908))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7908)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7908 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7908) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7908))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7908)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7909 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7909) = g32p_row31_cosetRepresentatives 7909 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7909 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7909) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7909))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7909)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7909 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7909) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7909))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7909)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7910 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7910) = g32p_row31_cosetRepresentatives 7910 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7910 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7910) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7910))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7910)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7910 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7910) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7910))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7910)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7911 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7911) = g32p_row31_cosetRepresentatives 7911 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7911 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7911) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7911))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7911)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7911 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7911) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7911))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7911)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7912 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7912) = g32p_row31_cosetRepresentatives 7912 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7912 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7912) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7912))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7912)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7912 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7912) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7912))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7912)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7913 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7913) = g32p_row31_cosetRepresentatives 7913 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7913 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7913) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7913))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7913)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7913 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7913) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7913))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7913)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7914 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7914) = g32p_row31_cosetRepresentatives 7914 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7914 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7914) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7914))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7914)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7914 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7914) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7914))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7914)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7915 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7915) = g32p_row31_cosetRepresentatives 7915 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7915 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7915) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7915))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7915)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7915 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7915) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7915))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7915)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7916 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7916) = g32p_row31_cosetRepresentatives 7916 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7916 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7916) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7916))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7916)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7916 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7916) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7916))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7916)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7917 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7917) = g32p_row31_cosetRepresentatives 7917 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7917 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7917) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7917))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7917)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7917 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7917) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7917))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7917)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7918 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7918) = g32p_row31_cosetRepresentatives 7918 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7918 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7918) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7918))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7918)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7918 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7918) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7918))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7918)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7919 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7919) = g32p_row31_cosetRepresentatives 7919 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7919 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7919) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7919))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7919)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7919 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7919) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7919))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7919)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0494 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 494 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 494 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7904
  · exact g32p_row31_cosetWord_7905
  · exact g32p_row31_cosetWord_7906
  · exact g32p_row31_cosetWord_7907
  · exact g32p_row31_cosetWord_7908
  · exact g32p_row31_cosetWord_7909
  · exact g32p_row31_cosetWord_7910
  · exact g32p_row31_cosetWord_7911
  · exact g32p_row31_cosetWord_7912
  · exact g32p_row31_cosetWord_7913
  · exact g32p_row31_cosetWord_7914
  · exact g32p_row31_cosetWord_7915
  · exact g32p_row31_cosetWord_7916
  · exact g32p_row31_cosetWord_7917
  · exact g32p_row31_cosetWord_7918
  · exact g32p_row31_cosetWord_7919

theorem g32p_row31_cosetGeneratorBlock_0494 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 494 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 494 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 494 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7904 s
  · exact g32p_row31_cosetGeneratorStep_7905 s
  · exact g32p_row31_cosetGeneratorStep_7906 s
  · exact g32p_row31_cosetGeneratorStep_7907 s
  · exact g32p_row31_cosetGeneratorStep_7908 s
  · exact g32p_row31_cosetGeneratorStep_7909 s
  · exact g32p_row31_cosetGeneratorStep_7910 s
  · exact g32p_row31_cosetGeneratorStep_7911 s
  · exact g32p_row31_cosetGeneratorStep_7912 s
  · exact g32p_row31_cosetGeneratorStep_7913 s
  · exact g32p_row31_cosetGeneratorStep_7914 s
  · exact g32p_row31_cosetGeneratorStep_7915 s
  · exact g32p_row31_cosetGeneratorStep_7916 s
  · exact g32p_row31_cosetGeneratorStep_7917 s
  · exact g32p_row31_cosetGeneratorStep_7918 s
  · exact g32p_row31_cosetGeneratorStep_7919 s

theorem g32p_row31_cosetBranchBlock_0494 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 494 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 494 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 494 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7904 s
  · exact g32p_row31_cosetBranchStep_7905 s
  · exact g32p_row31_cosetBranchStep_7906 s
  · exact g32p_row31_cosetBranchStep_7907 s
  · exact g32p_row31_cosetBranchStep_7908 s
  · exact g32p_row31_cosetBranchStep_7909 s
  · exact g32p_row31_cosetBranchStep_7910 s
  · exact g32p_row31_cosetBranchStep_7911 s
  · exact g32p_row31_cosetBranchStep_7912 s
  · exact g32p_row31_cosetBranchStep_7913 s
  · exact g32p_row31_cosetBranchStep_7914 s
  · exact g32p_row31_cosetBranchStep_7915 s
  · exact g32p_row31_cosetBranchStep_7916 s
  · exact g32p_row31_cosetBranchStep_7917 s
  · exact g32p_row31_cosetBranchStep_7918 s
  · exact g32p_row31_cosetBranchStep_7919 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7920 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7920) = g32p_row31_cosetRepresentatives 7920 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7920 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7920) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7920))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7920)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7920 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7920) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7920))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7920)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7921 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7921) = g32p_row31_cosetRepresentatives 7921 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7921 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7921) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7921))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7921)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7921 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7921) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7921))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7921)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7922 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7922) = g32p_row31_cosetRepresentatives 7922 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7922 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7922) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7922))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7922)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7922 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7922) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7922))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7922)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7923 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7923) = g32p_row31_cosetRepresentatives 7923 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7923 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7923) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7923))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7923)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7923 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7923) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7923))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7923)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7924 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7924) = g32p_row31_cosetRepresentatives 7924 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7924 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7924) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7924))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7924)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7924 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7924) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7924))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7924)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7925 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7925) = g32p_row31_cosetRepresentatives 7925 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7925 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7925) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7925))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7925)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7925 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7925) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7925))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7925)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7926 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7926) = g32p_row31_cosetRepresentatives 7926 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7926 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7926) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7926))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7926)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7926 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7926) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7926))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7926)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7927 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7927) = g32p_row31_cosetRepresentatives 7927 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7927 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7927) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7927))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7927)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7927 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7927) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7927))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7927)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7928 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7928) = g32p_row31_cosetRepresentatives 7928 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7928 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7928) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7928))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7928)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7928 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7928) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7928))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7928)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7929 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7929) = g32p_row31_cosetRepresentatives 7929 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7929 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7929) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7929))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7929)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7929 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7929) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7929))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7929)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7930 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7930) = g32p_row31_cosetRepresentatives 7930 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7930 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7930) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7930))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7930)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7930 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7930) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7930))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7930)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7931 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7931) = g32p_row31_cosetRepresentatives 7931 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7931 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7931) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7931))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7931)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7931 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7931) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7931))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7931)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7932 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7932) = g32p_row31_cosetRepresentatives 7932 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7932 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7932) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7932))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7932)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7932 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7932) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7932))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7932)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7933 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7933) = g32p_row31_cosetRepresentatives 7933 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7933 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7933) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7933))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7933)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7933 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7933) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7933))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7933)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7934 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7934) = g32p_row31_cosetRepresentatives 7934 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7934 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7934) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7934))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7934)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7934 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7934) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7934))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7934)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7935 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7935) = g32p_row31_cosetRepresentatives 7935 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7935 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7935) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7935))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7935)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7935 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7935) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7935))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7935)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0495 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 495 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 495 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7920
  · exact g32p_row31_cosetWord_7921
  · exact g32p_row31_cosetWord_7922
  · exact g32p_row31_cosetWord_7923
  · exact g32p_row31_cosetWord_7924
  · exact g32p_row31_cosetWord_7925
  · exact g32p_row31_cosetWord_7926
  · exact g32p_row31_cosetWord_7927
  · exact g32p_row31_cosetWord_7928
  · exact g32p_row31_cosetWord_7929
  · exact g32p_row31_cosetWord_7930
  · exact g32p_row31_cosetWord_7931
  · exact g32p_row31_cosetWord_7932
  · exact g32p_row31_cosetWord_7933
  · exact g32p_row31_cosetWord_7934
  · exact g32p_row31_cosetWord_7935

theorem g32p_row31_cosetGeneratorBlock_0495 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 495 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 495 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 495 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7920 s
  · exact g32p_row31_cosetGeneratorStep_7921 s
  · exact g32p_row31_cosetGeneratorStep_7922 s
  · exact g32p_row31_cosetGeneratorStep_7923 s
  · exact g32p_row31_cosetGeneratorStep_7924 s
  · exact g32p_row31_cosetGeneratorStep_7925 s
  · exact g32p_row31_cosetGeneratorStep_7926 s
  · exact g32p_row31_cosetGeneratorStep_7927 s
  · exact g32p_row31_cosetGeneratorStep_7928 s
  · exact g32p_row31_cosetGeneratorStep_7929 s
  · exact g32p_row31_cosetGeneratorStep_7930 s
  · exact g32p_row31_cosetGeneratorStep_7931 s
  · exact g32p_row31_cosetGeneratorStep_7932 s
  · exact g32p_row31_cosetGeneratorStep_7933 s
  · exact g32p_row31_cosetGeneratorStep_7934 s
  · exact g32p_row31_cosetGeneratorStep_7935 s

theorem g32p_row31_cosetBranchBlock_0495 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 495 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 495 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 495 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7920 s
  · exact g32p_row31_cosetBranchStep_7921 s
  · exact g32p_row31_cosetBranchStep_7922 s
  · exact g32p_row31_cosetBranchStep_7923 s
  · exact g32p_row31_cosetBranchStep_7924 s
  · exact g32p_row31_cosetBranchStep_7925 s
  · exact g32p_row31_cosetBranchStep_7926 s
  · exact g32p_row31_cosetBranchStep_7927 s
  · exact g32p_row31_cosetBranchStep_7928 s
  · exact g32p_row31_cosetBranchStep_7929 s
  · exact g32p_row31_cosetBranchStep_7930 s
  · exact g32p_row31_cosetBranchStep_7931 s
  · exact g32p_row31_cosetBranchStep_7932 s
  · exact g32p_row31_cosetBranchStep_7933 s
  · exact g32p_row31_cosetBranchStep_7934 s
  · exact g32p_row31_cosetBranchStep_7935 s


end HodgeLean.Foundations.Program

end
