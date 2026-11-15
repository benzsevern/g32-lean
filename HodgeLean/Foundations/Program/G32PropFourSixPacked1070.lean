import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked1044
import HodgeLean.Foundations.Program.G32PropFourSixPacked1045
import HodgeLean.Foundations.Program.G32PropFourSixPacked1046
import HodgeLean.Foundations.Program.G32PropFourSixPacked1047
import HodgeLean.Foundations.Program.G32PropFourSixPacked1048
import HodgeLean.Foundations.Program.G32PropFourSixPacked1049
import HodgeLean.Foundations.Program.G32PropFourSixPacked1050
import HodgeLean.Foundations.Program.G32PropFourSixPacked1051
import HodgeLean.Foundations.Program.G32PropFourSixPacked1052
import HodgeLean.Foundations.Program.G32PropFourSixPacked1053
import HodgeLean.Foundations.Program.G32PropFourSixPacked1054
import HodgeLean.Foundations.Program.G32PropFourSixPacked1055
import HodgeLean.Foundations.Program.G32PropFourSixPacked1056
import HodgeLean.Foundations.Program.G32PropFourSixPacked1057
import HodgeLean.Foundations.Program.G32PropFourSixPacked1058
import HodgeLean.Foundations.Program.G32PropFourSixPacked1059
import HodgeLean.Foundations.Program.G32PropFourSixPacked1060
import HodgeLean.Foundations.Program.G32PropFourSixPacked1061
import HodgeLean.Foundations.Program.G32PropFourSixPacked1062
import HodgeLean.Foundations.Program.G32PropFourSixPacked1063
import HodgeLean.Foundations.Program.G32PropFourSixPacked1064
import HodgeLean.Foundations.Program.G32PropFourSixPacked1065
import HodgeLean.Foundations.Program.G32PropFourSixPacked1066
import HodgeLean.Foundations.Program.G32PropFourSixPacked1067
import HodgeLean.Foundations.Program.G32PropFourSixPacked1068
import HodgeLean.Foundations.Program.G32PropFourSixPacked1069
import HodgeLean.Foundations.Program.G32PropFourSixPacked0629
import HodgeLean.Foundations.Program.G32PropFourSixPacked0494
import HodgeLean.Foundations.Program.G32PropFourSixPacked0634
import HodgeLean.Foundations.Program.G32PropFourSixPacked1030
import Mathlib.Data.Fin.Basic
import Lean.Elab.Tactic.Omega

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_6400 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6400) = g32p_row13_cosetRepresentatives 6400 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6400 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6400) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6400))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6400)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6400 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6400) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6400))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6400)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6401 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6401) = g32p_row13_cosetRepresentatives 6401 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6401 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6401) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6401))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6401)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6401 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6401) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6401))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6401)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6402 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6402) = g32p_row13_cosetRepresentatives 6402 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6402 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6402) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6402))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6402)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6402 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6402) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6402))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6402)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6403 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6403) = g32p_row13_cosetRepresentatives 6403 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6403 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6403) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6403))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6403)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6403 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6403) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6403))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6403)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6404 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6404) = g32p_row13_cosetRepresentatives 6404 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6404 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6404) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6404))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6404)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6404 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6404) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6404))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6404)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6405 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6405) = g32p_row13_cosetRepresentatives 6405 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6405 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6405) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6405))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6405)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6405 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6405) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6405))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6405)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6406 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6406) = g32p_row13_cosetRepresentatives 6406 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6406 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6406) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6406))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6406)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6406 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6406) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6406))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6406)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6407 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6407) = g32p_row13_cosetRepresentatives 6407 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6407 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6407) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6407))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6407)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6407 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6407) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6407))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6407)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6408 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6408) = g32p_row13_cosetRepresentatives 6408 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6408 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6408) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6408))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6408)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6408 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6408) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6408))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6408)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6409 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6409) = g32p_row13_cosetRepresentatives 6409 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6409 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6409) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6409))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6409)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6409 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6409) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6409))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6409)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6410 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6410) = g32p_row13_cosetRepresentatives 6410 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6410 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6410) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6410))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6410)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6410 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6410) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6410))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6410)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6411 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6411) = g32p_row13_cosetRepresentatives 6411 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6411 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6411) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6411))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6411)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6411 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6411) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6411))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6411)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6412 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6412) = g32p_row13_cosetRepresentatives 6412 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6412 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6412) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6412))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6412)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6412 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6412) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6412))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6412)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6413 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6413) = g32p_row13_cosetRepresentatives 6413 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6413 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6413) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6413))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6413)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6413 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6413) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6413))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6413)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6414 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6414) = g32p_row13_cosetRepresentatives 6414 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6414 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6414) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6414))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6414)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6414 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6414) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6414))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6414)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6415 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6415) = g32p_row13_cosetRepresentatives 6415 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6415 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6415) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6415))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6415)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6415 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6415) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6415))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6415)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0400 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 400 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 400 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_6400
  · exact g32p_row13_cosetWord_6401
  · exact g32p_row13_cosetWord_6402
  · exact g32p_row13_cosetWord_6403
  · exact g32p_row13_cosetWord_6404
  · exact g32p_row13_cosetWord_6405
  · exact g32p_row13_cosetWord_6406
  · exact g32p_row13_cosetWord_6407
  · exact g32p_row13_cosetWord_6408
  · exact g32p_row13_cosetWord_6409
  · exact g32p_row13_cosetWord_6410
  · exact g32p_row13_cosetWord_6411
  · exact g32p_row13_cosetWord_6412
  · exact g32p_row13_cosetWord_6413
  · exact g32p_row13_cosetWord_6414
  · exact g32p_row13_cosetWord_6415

theorem g32p_row13_cosetGeneratorBlock_0400 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 400 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 400 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 400 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_6400 s
  · exact g32p_row13_cosetGeneratorStep_6401 s
  · exact g32p_row13_cosetGeneratorStep_6402 s
  · exact g32p_row13_cosetGeneratorStep_6403 s
  · exact g32p_row13_cosetGeneratorStep_6404 s
  · exact g32p_row13_cosetGeneratorStep_6405 s
  · exact g32p_row13_cosetGeneratorStep_6406 s
  · exact g32p_row13_cosetGeneratorStep_6407 s
  · exact g32p_row13_cosetGeneratorStep_6408 s
  · exact g32p_row13_cosetGeneratorStep_6409 s
  · exact g32p_row13_cosetGeneratorStep_6410 s
  · exact g32p_row13_cosetGeneratorStep_6411 s
  · exact g32p_row13_cosetGeneratorStep_6412 s
  · exact g32p_row13_cosetGeneratorStep_6413 s
  · exact g32p_row13_cosetGeneratorStep_6414 s
  · exact g32p_row13_cosetGeneratorStep_6415 s

theorem g32p_row13_cosetBranchBlock_0400 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 400 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 400 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 400 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_6400 s
  · exact g32p_row13_cosetBranchStep_6401 s
  · exact g32p_row13_cosetBranchStep_6402 s
  · exact g32p_row13_cosetBranchStep_6403 s
  · exact g32p_row13_cosetBranchStep_6404 s
  · exact g32p_row13_cosetBranchStep_6405 s
  · exact g32p_row13_cosetBranchStep_6406 s
  · exact g32p_row13_cosetBranchStep_6407 s
  · exact g32p_row13_cosetBranchStep_6408 s
  · exact g32p_row13_cosetBranchStep_6409 s
  · exact g32p_row13_cosetBranchStep_6410 s
  · exact g32p_row13_cosetBranchStep_6411 s
  · exact g32p_row13_cosetBranchStep_6412 s
  · exact g32p_row13_cosetBranchStep_6413 s
  · exact g32p_row13_cosetBranchStep_6414 s
  · exact g32p_row13_cosetBranchStep_6415 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_6416 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6416) = g32p_row13_cosetRepresentatives 6416 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6416 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6416) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6416))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6416)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6416 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6416) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6416))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6416)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6417 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6417) = g32p_row13_cosetRepresentatives 6417 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6417 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6417) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6417))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6417)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6417 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6417) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6417))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6417)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6418 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6418) = g32p_row13_cosetRepresentatives 6418 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6418 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6418) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6418))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6418)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6418 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6418) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6418))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6418)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6419 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6419) = g32p_row13_cosetRepresentatives 6419 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6419 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6419) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6419))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6419)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6419 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6419) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6419))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6419)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6420 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6420) = g32p_row13_cosetRepresentatives 6420 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6420 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6420) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6420))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6420)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6420 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6420) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6420))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6420)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6421 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6421) = g32p_row13_cosetRepresentatives 6421 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6421 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6421) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6421))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6421)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6421 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6421) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6421))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6421)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6422 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6422) = g32p_row13_cosetRepresentatives 6422 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6422 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6422) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6422))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6422)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6422 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6422) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6422))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6422)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6423 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6423) = g32p_row13_cosetRepresentatives 6423 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6423 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6423) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6423))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6423)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6423 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6423) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6423))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6423)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6424 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6424) = g32p_row13_cosetRepresentatives 6424 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6424 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6424) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6424))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6424)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6424 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6424) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6424))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6424)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6425 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6425) = g32p_row13_cosetRepresentatives 6425 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6425 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6425) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6425))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6425)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6425 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6425) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6425))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6425)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6426 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6426) = g32p_row13_cosetRepresentatives 6426 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6426 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6426) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6426))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6426)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6426 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6426) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6426))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6426)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6427 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6427) = g32p_row13_cosetRepresentatives 6427 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6427 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6427) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6427))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6427)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6427 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6427) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6427))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6427)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6428 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6428) = g32p_row13_cosetRepresentatives 6428 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6428 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6428) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6428))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6428)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6428 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6428) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6428))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6428)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6429 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6429) = g32p_row13_cosetRepresentatives 6429 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6429 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6429) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6429))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6429)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6429 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6429) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6429))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6429)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6430 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6430) = g32p_row13_cosetRepresentatives 6430 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6430 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6430) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6430))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6430)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6430 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6430) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6430))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6430)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6431 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6431) = g32p_row13_cosetRepresentatives 6431 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6431 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6431) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6431))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6431)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6431 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6431) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6431))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6431)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0401 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 401 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 401 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_6416
  · exact g32p_row13_cosetWord_6417
  · exact g32p_row13_cosetWord_6418
  · exact g32p_row13_cosetWord_6419
  · exact g32p_row13_cosetWord_6420
  · exact g32p_row13_cosetWord_6421
  · exact g32p_row13_cosetWord_6422
  · exact g32p_row13_cosetWord_6423
  · exact g32p_row13_cosetWord_6424
  · exact g32p_row13_cosetWord_6425
  · exact g32p_row13_cosetWord_6426
  · exact g32p_row13_cosetWord_6427
  · exact g32p_row13_cosetWord_6428
  · exact g32p_row13_cosetWord_6429
  · exact g32p_row13_cosetWord_6430
  · exact g32p_row13_cosetWord_6431

theorem g32p_row13_cosetGeneratorBlock_0401 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 401 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 401 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 401 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_6416 s
  · exact g32p_row13_cosetGeneratorStep_6417 s
  · exact g32p_row13_cosetGeneratorStep_6418 s
  · exact g32p_row13_cosetGeneratorStep_6419 s
  · exact g32p_row13_cosetGeneratorStep_6420 s
  · exact g32p_row13_cosetGeneratorStep_6421 s
  · exact g32p_row13_cosetGeneratorStep_6422 s
  · exact g32p_row13_cosetGeneratorStep_6423 s
  · exact g32p_row13_cosetGeneratorStep_6424 s
  · exact g32p_row13_cosetGeneratorStep_6425 s
  · exact g32p_row13_cosetGeneratorStep_6426 s
  · exact g32p_row13_cosetGeneratorStep_6427 s
  · exact g32p_row13_cosetGeneratorStep_6428 s
  · exact g32p_row13_cosetGeneratorStep_6429 s
  · exact g32p_row13_cosetGeneratorStep_6430 s
  · exact g32p_row13_cosetGeneratorStep_6431 s

theorem g32p_row13_cosetBranchBlock_0401 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 401 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 401 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 401 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_6416 s
  · exact g32p_row13_cosetBranchStep_6417 s
  · exact g32p_row13_cosetBranchStep_6418 s
  · exact g32p_row13_cosetBranchStep_6419 s
  · exact g32p_row13_cosetBranchStep_6420 s
  · exact g32p_row13_cosetBranchStep_6421 s
  · exact g32p_row13_cosetBranchStep_6422 s
  · exact g32p_row13_cosetBranchStep_6423 s
  · exact g32p_row13_cosetBranchStep_6424 s
  · exact g32p_row13_cosetBranchStep_6425 s
  · exact g32p_row13_cosetBranchStep_6426 s
  · exact g32p_row13_cosetBranchStep_6427 s
  · exact g32p_row13_cosetBranchStep_6428 s
  · exact g32p_row13_cosetBranchStep_6429 s
  · exact g32p_row13_cosetBranchStep_6430 s
  · exact g32p_row13_cosetBranchStep_6431 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_6432 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6432) = g32p_row13_cosetRepresentatives 6432 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6432 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6432) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6432))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6432)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6432 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6432) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6432))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6432)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6433 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6433) = g32p_row13_cosetRepresentatives 6433 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6433 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6433) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6433))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6433)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6433 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6433) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6433))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6433)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6434 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6434) = g32p_row13_cosetRepresentatives 6434 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6434 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6434) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6434))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6434)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6434 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6434) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6434))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6434)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6435 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6435) = g32p_row13_cosetRepresentatives 6435 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6435 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6435) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6435))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6435)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6435 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6435) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6435))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6435)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6436 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6436) = g32p_row13_cosetRepresentatives 6436 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6436 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6436) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6436))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6436)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6436 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6436) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6436))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6436)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6437 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6437) = g32p_row13_cosetRepresentatives 6437 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6437 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6437) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6437))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6437)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6437 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6437) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6437))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6437)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6438 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6438) = g32p_row13_cosetRepresentatives 6438 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6438 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6438) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6438))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6438)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6438 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6438) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6438))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6438)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6439 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6439) = g32p_row13_cosetRepresentatives 6439 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6439 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6439) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6439))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6439)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6439 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6439) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6439))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6439)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6440 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6440) = g32p_row13_cosetRepresentatives 6440 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6440 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6440) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6440))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6440)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6440 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6440) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6440))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6440)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6441 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6441) = g32p_row13_cosetRepresentatives 6441 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6441 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6441) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6441))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6441)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6441 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6441) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6441))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6441)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6442 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6442) = g32p_row13_cosetRepresentatives 6442 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6442 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6442) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6442))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6442)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6442 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6442) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6442))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6442)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6443 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6443) = g32p_row13_cosetRepresentatives 6443 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6443 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6443) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6443))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6443)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6443 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6443) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6443))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6443)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6444 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6444) = g32p_row13_cosetRepresentatives 6444 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6444 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6444) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6444))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6444)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6444 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6444) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6444))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6444)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6445 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6445) = g32p_row13_cosetRepresentatives 6445 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6445 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6445) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6445))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6445)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6445 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6445) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6445))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6445)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6446 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6446) = g32p_row13_cosetRepresentatives 6446 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6446 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6446) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6446))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6446)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6446 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6446) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6446))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6446)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6447 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6447) = g32p_row13_cosetRepresentatives 6447 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6447 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6447) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6447))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6447)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6447 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6447) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6447))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6447)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0402 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 402 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 402 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_6432
  · exact g32p_row13_cosetWord_6433
  · exact g32p_row13_cosetWord_6434
  · exact g32p_row13_cosetWord_6435
  · exact g32p_row13_cosetWord_6436
  · exact g32p_row13_cosetWord_6437
  · exact g32p_row13_cosetWord_6438
  · exact g32p_row13_cosetWord_6439
  · exact g32p_row13_cosetWord_6440
  · exact g32p_row13_cosetWord_6441
  · exact g32p_row13_cosetWord_6442
  · exact g32p_row13_cosetWord_6443
  · exact g32p_row13_cosetWord_6444
  · exact g32p_row13_cosetWord_6445
  · exact g32p_row13_cosetWord_6446
  · exact g32p_row13_cosetWord_6447

theorem g32p_row13_cosetGeneratorBlock_0402 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 402 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 402 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 402 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_6432 s
  · exact g32p_row13_cosetGeneratorStep_6433 s
  · exact g32p_row13_cosetGeneratorStep_6434 s
  · exact g32p_row13_cosetGeneratorStep_6435 s
  · exact g32p_row13_cosetGeneratorStep_6436 s
  · exact g32p_row13_cosetGeneratorStep_6437 s
  · exact g32p_row13_cosetGeneratorStep_6438 s
  · exact g32p_row13_cosetGeneratorStep_6439 s
  · exact g32p_row13_cosetGeneratorStep_6440 s
  · exact g32p_row13_cosetGeneratorStep_6441 s
  · exact g32p_row13_cosetGeneratorStep_6442 s
  · exact g32p_row13_cosetGeneratorStep_6443 s
  · exact g32p_row13_cosetGeneratorStep_6444 s
  · exact g32p_row13_cosetGeneratorStep_6445 s
  · exact g32p_row13_cosetGeneratorStep_6446 s
  · exact g32p_row13_cosetGeneratorStep_6447 s

theorem g32p_row13_cosetBranchBlock_0402 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 402 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 402 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 402 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_6432 s
  · exact g32p_row13_cosetBranchStep_6433 s
  · exact g32p_row13_cosetBranchStep_6434 s
  · exact g32p_row13_cosetBranchStep_6435 s
  · exact g32p_row13_cosetBranchStep_6436 s
  · exact g32p_row13_cosetBranchStep_6437 s
  · exact g32p_row13_cosetBranchStep_6438 s
  · exact g32p_row13_cosetBranchStep_6439 s
  · exact g32p_row13_cosetBranchStep_6440 s
  · exact g32p_row13_cosetBranchStep_6441 s
  · exact g32p_row13_cosetBranchStep_6442 s
  · exact g32p_row13_cosetBranchStep_6443 s
  · exact g32p_row13_cosetBranchStep_6444 s
  · exact g32p_row13_cosetBranchStep_6445 s
  · exact g32p_row13_cosetBranchStep_6446 s
  · exact g32p_row13_cosetBranchStep_6447 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_6448 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6448) = g32p_row13_cosetRepresentatives 6448 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6448 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6448) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6448))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6448)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6448 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6448) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6448))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6448)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6449 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6449) = g32p_row13_cosetRepresentatives 6449 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6449 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6449) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6449))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6449)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6449 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6449) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6449))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6449)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6450 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6450) = g32p_row13_cosetRepresentatives 6450 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6450 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6450) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6450))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6450)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6450 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6450) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6450))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6450)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6451 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6451) = g32p_row13_cosetRepresentatives 6451 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6451 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6451) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6451))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6451)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6451 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6451) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6451))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6451)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6452 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6452) = g32p_row13_cosetRepresentatives 6452 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6452 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6452) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6452))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6452)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6452 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6452) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6452))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6452)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6453 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6453) = g32p_row13_cosetRepresentatives 6453 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6453 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6453) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6453))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6453)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6453 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6453) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6453))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6453)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6454 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6454) = g32p_row13_cosetRepresentatives 6454 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6454 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6454) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6454))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6454)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6454 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6454) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6454))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6454)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6455 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6455) = g32p_row13_cosetRepresentatives 6455 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6455 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6455) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6455))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6455)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6455 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6455) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6455))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6455)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6456 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6456) = g32p_row13_cosetRepresentatives 6456 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6456 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6456) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6456))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6456)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6456 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6456) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6456))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6456)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6457 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6457) = g32p_row13_cosetRepresentatives 6457 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6457 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6457) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6457))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6457)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6457 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6457) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6457))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6457)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6458 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6458) = g32p_row13_cosetRepresentatives 6458 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6458 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6458) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6458))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6458)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6458 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6458) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6458))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6458)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6459 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6459) = g32p_row13_cosetRepresentatives 6459 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6459 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6459) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6459))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6459)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6459 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6459) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6459))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6459)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6460 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6460) = g32p_row13_cosetRepresentatives 6460 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6460 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6460) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6460))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6460)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6460 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6460) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6460))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6460)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6461 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6461) = g32p_row13_cosetRepresentatives 6461 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6461 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6461) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6461))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6461)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6461 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6461) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6461))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6461)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6462 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6462) = g32p_row13_cosetRepresentatives 6462 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6462 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6462) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6462))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6462)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6462 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6462) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6462))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6462)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6463 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6463) = g32p_row13_cosetRepresentatives 6463 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6463 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6463) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6463))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6463)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6463 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6463) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6463))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6463)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0403 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 403 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 403 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_6448
  · exact g32p_row13_cosetWord_6449
  · exact g32p_row13_cosetWord_6450
  · exact g32p_row13_cosetWord_6451
  · exact g32p_row13_cosetWord_6452
  · exact g32p_row13_cosetWord_6453
  · exact g32p_row13_cosetWord_6454
  · exact g32p_row13_cosetWord_6455
  · exact g32p_row13_cosetWord_6456
  · exact g32p_row13_cosetWord_6457
  · exact g32p_row13_cosetWord_6458
  · exact g32p_row13_cosetWord_6459
  · exact g32p_row13_cosetWord_6460
  · exact g32p_row13_cosetWord_6461
  · exact g32p_row13_cosetWord_6462
  · exact g32p_row13_cosetWord_6463

theorem g32p_row13_cosetGeneratorBlock_0403 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 403 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 403 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 403 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_6448 s
  · exact g32p_row13_cosetGeneratorStep_6449 s
  · exact g32p_row13_cosetGeneratorStep_6450 s
  · exact g32p_row13_cosetGeneratorStep_6451 s
  · exact g32p_row13_cosetGeneratorStep_6452 s
  · exact g32p_row13_cosetGeneratorStep_6453 s
  · exact g32p_row13_cosetGeneratorStep_6454 s
  · exact g32p_row13_cosetGeneratorStep_6455 s
  · exact g32p_row13_cosetGeneratorStep_6456 s
  · exact g32p_row13_cosetGeneratorStep_6457 s
  · exact g32p_row13_cosetGeneratorStep_6458 s
  · exact g32p_row13_cosetGeneratorStep_6459 s
  · exact g32p_row13_cosetGeneratorStep_6460 s
  · exact g32p_row13_cosetGeneratorStep_6461 s
  · exact g32p_row13_cosetGeneratorStep_6462 s
  · exact g32p_row13_cosetGeneratorStep_6463 s

theorem g32p_row13_cosetBranchBlock_0403 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 403 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 403 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 403 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_6448 s
  · exact g32p_row13_cosetBranchStep_6449 s
  · exact g32p_row13_cosetBranchStep_6450 s
  · exact g32p_row13_cosetBranchStep_6451 s
  · exact g32p_row13_cosetBranchStep_6452 s
  · exact g32p_row13_cosetBranchStep_6453 s
  · exact g32p_row13_cosetBranchStep_6454 s
  · exact g32p_row13_cosetBranchStep_6455 s
  · exact g32p_row13_cosetBranchStep_6456 s
  · exact g32p_row13_cosetBranchStep_6457 s
  · exact g32p_row13_cosetBranchStep_6458 s
  · exact g32p_row13_cosetBranchStep_6459 s
  · exact g32p_row13_cosetBranchStep_6460 s
  · exact g32p_row13_cosetBranchStep_6461 s
  · exact g32p_row13_cosetBranchStep_6462 s
  · exact g32p_row13_cosetBranchStep_6463 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_6464 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6464) = g32p_row13_cosetRepresentatives 6464 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6464 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6464) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6464))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6464)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6464 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6464) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6464))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6464)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6465 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6465) = g32p_row13_cosetRepresentatives 6465 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6465 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6465) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6465))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6465)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6465 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6465) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6465))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6465)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6466 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6466) = g32p_row13_cosetRepresentatives 6466 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6466 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6466) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6466))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6466)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6466 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6466) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6466))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6466)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6467 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6467) = g32p_row13_cosetRepresentatives 6467 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6467 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6467) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6467))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6467)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6467 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6467) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6467))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6467)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6468 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6468) = g32p_row13_cosetRepresentatives 6468 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6468 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6468) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6468))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6468)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6468 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6468) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6468))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6468)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6469 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6469) = g32p_row13_cosetRepresentatives 6469 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6469 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6469) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6469))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6469)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6469 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6469) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6469))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6469)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6470 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6470) = g32p_row13_cosetRepresentatives 6470 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6470 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6470) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6470))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6470)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6470 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6470) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6470))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6470)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6471 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6471) = g32p_row13_cosetRepresentatives 6471 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6471 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6471) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6471))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6471)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6471 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6471) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6471))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6471)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6472 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6472) = g32p_row13_cosetRepresentatives 6472 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6472 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6472) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6472))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6472)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6472 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6472) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6472))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6472)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6473 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6473) = g32p_row13_cosetRepresentatives 6473 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6473 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6473) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6473))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6473)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6473 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6473) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6473))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6473)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6474 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6474) = g32p_row13_cosetRepresentatives 6474 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6474 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6474) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6474))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6474)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6474 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6474) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6474))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6474)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6475 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6475) = g32p_row13_cosetRepresentatives 6475 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6475 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6475) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6475))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6475)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6475 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6475) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6475))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6475)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6476 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6476) = g32p_row13_cosetRepresentatives 6476 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6476 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6476) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6476))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6476)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6476 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6476) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6476))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6476)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6477 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6477) = g32p_row13_cosetRepresentatives 6477 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6477 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6477) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6477))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6477)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6477 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6477) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6477))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6477)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6478 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6478) = g32p_row13_cosetRepresentatives 6478 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6478 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6478) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6478))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6478)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6478 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6478) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6478))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6478)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6479 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6479) = g32p_row13_cosetRepresentatives 6479 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6479 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6479) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6479))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6479)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6479 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6479) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6479))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6479)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0404 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 404 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 404 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_6464
  · exact g32p_row13_cosetWord_6465
  · exact g32p_row13_cosetWord_6466
  · exact g32p_row13_cosetWord_6467
  · exact g32p_row13_cosetWord_6468
  · exact g32p_row13_cosetWord_6469
  · exact g32p_row13_cosetWord_6470
  · exact g32p_row13_cosetWord_6471
  · exact g32p_row13_cosetWord_6472
  · exact g32p_row13_cosetWord_6473
  · exact g32p_row13_cosetWord_6474
  · exact g32p_row13_cosetWord_6475
  · exact g32p_row13_cosetWord_6476
  · exact g32p_row13_cosetWord_6477
  · exact g32p_row13_cosetWord_6478
  · exact g32p_row13_cosetWord_6479

theorem g32p_row13_cosetGeneratorBlock_0404 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 404 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 404 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 404 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_6464 s
  · exact g32p_row13_cosetGeneratorStep_6465 s
  · exact g32p_row13_cosetGeneratorStep_6466 s
  · exact g32p_row13_cosetGeneratorStep_6467 s
  · exact g32p_row13_cosetGeneratorStep_6468 s
  · exact g32p_row13_cosetGeneratorStep_6469 s
  · exact g32p_row13_cosetGeneratorStep_6470 s
  · exact g32p_row13_cosetGeneratorStep_6471 s
  · exact g32p_row13_cosetGeneratorStep_6472 s
  · exact g32p_row13_cosetGeneratorStep_6473 s
  · exact g32p_row13_cosetGeneratorStep_6474 s
  · exact g32p_row13_cosetGeneratorStep_6475 s
  · exact g32p_row13_cosetGeneratorStep_6476 s
  · exact g32p_row13_cosetGeneratorStep_6477 s
  · exact g32p_row13_cosetGeneratorStep_6478 s
  · exact g32p_row13_cosetGeneratorStep_6479 s

theorem g32p_row13_cosetBranchBlock_0404 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 404 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 404 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 404 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_6464 s
  · exact g32p_row13_cosetBranchStep_6465 s
  · exact g32p_row13_cosetBranchStep_6466 s
  · exact g32p_row13_cosetBranchStep_6467 s
  · exact g32p_row13_cosetBranchStep_6468 s
  · exact g32p_row13_cosetBranchStep_6469 s
  · exact g32p_row13_cosetBranchStep_6470 s
  · exact g32p_row13_cosetBranchStep_6471 s
  · exact g32p_row13_cosetBranchStep_6472 s
  · exact g32p_row13_cosetBranchStep_6473 s
  · exact g32p_row13_cosetBranchStep_6474 s
  · exact g32p_row13_cosetBranchStep_6475 s
  · exact g32p_row13_cosetBranchStep_6476 s
  · exact g32p_row13_cosetBranchStep_6477 s
  · exact g32p_row13_cosetBranchStep_6478 s
  · exact g32p_row13_cosetBranchStep_6479 s


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

theorem g32p_row13_cosetWord (i : Fin 6480) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords i) = g32p_row13_cosetRepresentatives i := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row13_cosetWordBlock_0000
  · exact g32p_row13_cosetWordBlock_0001
  · exact g32p_row13_cosetWordBlock_0002
  · exact g32p_row13_cosetWordBlock_0003
  · exact g32p_row13_cosetWordBlock_0004
  · exact g32p_row13_cosetWordBlock_0005
  · exact g32p_row13_cosetWordBlock_0006
  · exact g32p_row13_cosetWordBlock_0007
  · exact g32p_row13_cosetWordBlock_0008
  · exact g32p_row13_cosetWordBlock_0009
  · exact g32p_row13_cosetWordBlock_0010
  · exact g32p_row13_cosetWordBlock_0011
  · exact g32p_row13_cosetWordBlock_0012
  · exact g32p_row13_cosetWordBlock_0013
  · exact g32p_row13_cosetWordBlock_0014
  · exact g32p_row13_cosetWordBlock_0015
  · exact g32p_row13_cosetWordBlock_0016
  · exact g32p_row13_cosetWordBlock_0017
  · exact g32p_row13_cosetWordBlock_0018
  · exact g32p_row13_cosetWordBlock_0019
  · exact g32p_row13_cosetWordBlock_0020
  · exact g32p_row13_cosetWordBlock_0021
  · exact g32p_row13_cosetWordBlock_0022
  · exact g32p_row13_cosetWordBlock_0023
  · exact g32p_row13_cosetWordBlock_0024
  · exact g32p_row13_cosetWordBlock_0025
  · exact g32p_row13_cosetWordBlock_0026
  · exact g32p_row13_cosetWordBlock_0027
  · exact g32p_row13_cosetWordBlock_0028
  · exact g32p_row13_cosetWordBlock_0029
  · exact g32p_row13_cosetWordBlock_0030
  · exact g32p_row13_cosetWordBlock_0031
  · exact g32p_row13_cosetWordBlock_0032
  · exact g32p_row13_cosetWordBlock_0033
  · exact g32p_row13_cosetWordBlock_0034
  · exact g32p_row13_cosetWordBlock_0035
  · exact g32p_row13_cosetWordBlock_0036
  · exact g32p_row13_cosetWordBlock_0037
  · exact g32p_row13_cosetWordBlock_0038
  · exact g32p_row13_cosetWordBlock_0039
  · exact g32p_row13_cosetWordBlock_0040
  · exact g32p_row13_cosetWordBlock_0041
  · exact g32p_row13_cosetWordBlock_0042
  · exact g32p_row13_cosetWordBlock_0043
  · exact g32p_row13_cosetWordBlock_0044
  · exact g32p_row13_cosetWordBlock_0045
  · exact g32p_row13_cosetWordBlock_0046
  · exact g32p_row13_cosetWordBlock_0047
  · exact g32p_row13_cosetWordBlock_0048
  · exact g32p_row13_cosetWordBlock_0049
  · exact g32p_row13_cosetWordBlock_0050
  · exact g32p_row13_cosetWordBlock_0051
  · exact g32p_row13_cosetWordBlock_0052
  · exact g32p_row13_cosetWordBlock_0053
  · exact g32p_row13_cosetWordBlock_0054
  · exact g32p_row13_cosetWordBlock_0055
  · exact g32p_row13_cosetWordBlock_0056
  · exact g32p_row13_cosetWordBlock_0057
  · exact g32p_row13_cosetWordBlock_0058
  · exact g32p_row13_cosetWordBlock_0059
  · exact g32p_row13_cosetWordBlock_0060
  · exact g32p_row13_cosetWordBlock_0061
  · exact g32p_row13_cosetWordBlock_0062
  · exact g32p_row13_cosetWordBlock_0063
  · exact g32p_row13_cosetWordBlock_0064
  · exact g32p_row13_cosetWordBlock_0065
  · exact g32p_row13_cosetWordBlock_0066
  · exact g32p_row13_cosetWordBlock_0067
  · exact g32p_row13_cosetWordBlock_0068
  · exact g32p_row13_cosetWordBlock_0069
  · exact g32p_row13_cosetWordBlock_0070
  · exact g32p_row13_cosetWordBlock_0071
  · exact g32p_row13_cosetWordBlock_0072
  · exact g32p_row13_cosetWordBlock_0073
  · exact g32p_row13_cosetWordBlock_0074
  · exact g32p_row13_cosetWordBlock_0075
  · exact g32p_row13_cosetWordBlock_0076
  · exact g32p_row13_cosetWordBlock_0077
  · exact g32p_row13_cosetWordBlock_0078
  · exact g32p_row13_cosetWordBlock_0079
  · exact g32p_row13_cosetWordBlock_0080
  · exact g32p_row13_cosetWordBlock_0081
  · exact g32p_row13_cosetWordBlock_0082
  · exact g32p_row13_cosetWordBlock_0083
  · exact g32p_row13_cosetWordBlock_0084
  · exact g32p_row13_cosetWordBlock_0085
  · exact g32p_row13_cosetWordBlock_0086
  · exact g32p_row13_cosetWordBlock_0087
  · exact g32p_row13_cosetWordBlock_0088
  · exact g32p_row13_cosetWordBlock_0089
  · exact g32p_row13_cosetWordBlock_0090
  · exact g32p_row13_cosetWordBlock_0091
  · exact g32p_row13_cosetWordBlock_0092
  · exact g32p_row13_cosetWordBlock_0093
  · exact g32p_row13_cosetWordBlock_0094
  · exact g32p_row13_cosetWordBlock_0095
  · exact g32p_row13_cosetWordBlock_0096
  · exact g32p_row13_cosetWordBlock_0097
  · exact g32p_row13_cosetWordBlock_0098
  · exact g32p_row13_cosetWordBlock_0099
  · exact g32p_row13_cosetWordBlock_0100
  · exact g32p_row13_cosetWordBlock_0101
  · exact g32p_row13_cosetWordBlock_0102
  · exact g32p_row13_cosetWordBlock_0103
  · exact g32p_row13_cosetWordBlock_0104
  · exact g32p_row13_cosetWordBlock_0105
  · exact g32p_row13_cosetWordBlock_0106
  · exact g32p_row13_cosetWordBlock_0107
  · exact g32p_row13_cosetWordBlock_0108
  · exact g32p_row13_cosetWordBlock_0109
  · exact g32p_row13_cosetWordBlock_0110
  · exact g32p_row13_cosetWordBlock_0111
  · exact g32p_row13_cosetWordBlock_0112
  · exact g32p_row13_cosetWordBlock_0113
  · exact g32p_row13_cosetWordBlock_0114
  · exact g32p_row13_cosetWordBlock_0115
  · exact g32p_row13_cosetWordBlock_0116
  · exact g32p_row13_cosetWordBlock_0117
  · exact g32p_row13_cosetWordBlock_0118
  · exact g32p_row13_cosetWordBlock_0119
  · exact g32p_row13_cosetWordBlock_0120
  · exact g32p_row13_cosetWordBlock_0121
  · exact g32p_row13_cosetWordBlock_0122
  · exact g32p_row13_cosetWordBlock_0123
  · exact g32p_row13_cosetWordBlock_0124
  · exact g32p_row13_cosetWordBlock_0125
  · exact g32p_row13_cosetWordBlock_0126
  · exact g32p_row13_cosetWordBlock_0127
  · exact g32p_row13_cosetWordBlock_0128
  · exact g32p_row13_cosetWordBlock_0129
  · exact g32p_row13_cosetWordBlock_0130
  · exact g32p_row13_cosetWordBlock_0131
  · exact g32p_row13_cosetWordBlock_0132
  · exact g32p_row13_cosetWordBlock_0133
  · exact g32p_row13_cosetWordBlock_0134
  · exact g32p_row13_cosetWordBlock_0135
  · exact g32p_row13_cosetWordBlock_0136
  · exact g32p_row13_cosetWordBlock_0137
  · exact g32p_row13_cosetWordBlock_0138
  · exact g32p_row13_cosetWordBlock_0139
  · exact g32p_row13_cosetWordBlock_0140
  · exact g32p_row13_cosetWordBlock_0141
  · exact g32p_row13_cosetWordBlock_0142
  · exact g32p_row13_cosetWordBlock_0143
  · exact g32p_row13_cosetWordBlock_0144
  · exact g32p_row13_cosetWordBlock_0145
  · exact g32p_row13_cosetWordBlock_0146
  · exact g32p_row13_cosetWordBlock_0147
  · exact g32p_row13_cosetWordBlock_0148
  · exact g32p_row13_cosetWordBlock_0149
  · exact g32p_row13_cosetWordBlock_0150
  · exact g32p_row13_cosetWordBlock_0151
  · exact g32p_row13_cosetWordBlock_0152
  · exact g32p_row13_cosetWordBlock_0153
  · exact g32p_row13_cosetWordBlock_0154
  · exact g32p_row13_cosetWordBlock_0155
  · exact g32p_row13_cosetWordBlock_0156
  · exact g32p_row13_cosetWordBlock_0157
  · exact g32p_row13_cosetWordBlock_0158
  · exact g32p_row13_cosetWordBlock_0159
  · exact g32p_row13_cosetWordBlock_0160
  · exact g32p_row13_cosetWordBlock_0161
  · exact g32p_row13_cosetWordBlock_0162
  · exact g32p_row13_cosetWordBlock_0163
  · exact g32p_row13_cosetWordBlock_0164
  · exact g32p_row13_cosetWordBlock_0165
  · exact g32p_row13_cosetWordBlock_0166
  · exact g32p_row13_cosetWordBlock_0167
  · exact g32p_row13_cosetWordBlock_0168
  · exact g32p_row13_cosetWordBlock_0169
  · exact g32p_row13_cosetWordBlock_0170
  · exact g32p_row13_cosetWordBlock_0171
  · exact g32p_row13_cosetWordBlock_0172
  · exact g32p_row13_cosetWordBlock_0173
  · exact g32p_row13_cosetWordBlock_0174
  · exact g32p_row13_cosetWordBlock_0175
  · exact g32p_row13_cosetWordBlock_0176
  · exact g32p_row13_cosetWordBlock_0177
  · exact g32p_row13_cosetWordBlock_0178
  · exact g32p_row13_cosetWordBlock_0179
  · exact g32p_row13_cosetWordBlock_0180
  · exact g32p_row13_cosetWordBlock_0181
  · exact g32p_row13_cosetWordBlock_0182
  · exact g32p_row13_cosetWordBlock_0183
  · exact g32p_row13_cosetWordBlock_0184
  · exact g32p_row13_cosetWordBlock_0185
  · exact g32p_row13_cosetWordBlock_0186
  · exact g32p_row13_cosetWordBlock_0187
  · exact g32p_row13_cosetWordBlock_0188
  · exact g32p_row13_cosetWordBlock_0189
  · exact g32p_row13_cosetWordBlock_0190
  · exact g32p_row13_cosetWordBlock_0191
  · exact g32p_row13_cosetWordBlock_0192
  · exact g32p_row13_cosetWordBlock_0193
  · exact g32p_row13_cosetWordBlock_0194
  · exact g32p_row13_cosetWordBlock_0195
  · exact g32p_row13_cosetWordBlock_0196
  · exact g32p_row13_cosetWordBlock_0197
  · exact g32p_row13_cosetWordBlock_0198
  · exact g32p_row13_cosetWordBlock_0199
  · exact g32p_row13_cosetWordBlock_0200
  · exact g32p_row13_cosetWordBlock_0201
  · exact g32p_row13_cosetWordBlock_0202
  · exact g32p_row13_cosetWordBlock_0203
  · exact g32p_row13_cosetWordBlock_0204
  · exact g32p_row13_cosetWordBlock_0205
  · exact g32p_row13_cosetWordBlock_0206
  · exact g32p_row13_cosetWordBlock_0207
  · exact g32p_row13_cosetWordBlock_0208
  · exact g32p_row13_cosetWordBlock_0209
  · exact g32p_row13_cosetWordBlock_0210
  · exact g32p_row13_cosetWordBlock_0211
  · exact g32p_row13_cosetWordBlock_0212
  · exact g32p_row13_cosetWordBlock_0213
  · exact g32p_row13_cosetWordBlock_0214
  · exact g32p_row13_cosetWordBlock_0215
  · exact g32p_row13_cosetWordBlock_0216
  · exact g32p_row13_cosetWordBlock_0217
  · exact g32p_row13_cosetWordBlock_0218
  · exact g32p_row13_cosetWordBlock_0219
  · exact g32p_row13_cosetWordBlock_0220
  · exact g32p_row13_cosetWordBlock_0221
  · exact g32p_row13_cosetWordBlock_0222
  · exact g32p_row13_cosetWordBlock_0223
  · exact g32p_row13_cosetWordBlock_0224
  · exact g32p_row13_cosetWordBlock_0225
  · exact g32p_row13_cosetWordBlock_0226
  · exact g32p_row13_cosetWordBlock_0227
  · exact g32p_row13_cosetWordBlock_0228
  · exact g32p_row13_cosetWordBlock_0229
  · exact g32p_row13_cosetWordBlock_0230
  · exact g32p_row13_cosetWordBlock_0231
  · exact g32p_row13_cosetWordBlock_0232
  · exact g32p_row13_cosetWordBlock_0233
  · exact g32p_row13_cosetWordBlock_0234
  · exact g32p_row13_cosetWordBlock_0235
  · exact g32p_row13_cosetWordBlock_0236
  · exact g32p_row13_cosetWordBlock_0237
  · exact g32p_row13_cosetWordBlock_0238
  · exact g32p_row13_cosetWordBlock_0239
  · exact g32p_row13_cosetWordBlock_0240
  · exact g32p_row13_cosetWordBlock_0241
  · exact g32p_row13_cosetWordBlock_0242
  · exact g32p_row13_cosetWordBlock_0243
  · exact g32p_row13_cosetWordBlock_0244
  · exact g32p_row13_cosetWordBlock_0245
  · exact g32p_row13_cosetWordBlock_0246
  · exact g32p_row13_cosetWordBlock_0247
  · exact g32p_row13_cosetWordBlock_0248
  · exact g32p_row13_cosetWordBlock_0249
  · exact g32p_row13_cosetWordBlock_0250
  · exact g32p_row13_cosetWordBlock_0251
  · exact g32p_row13_cosetWordBlock_0252
  · exact g32p_row13_cosetWordBlock_0253
  · exact g32p_row13_cosetWordBlock_0254
  · exact g32p_row13_cosetWordBlock_0255
  · exact g32p_row13_cosetWordBlock_0256
  · exact g32p_row13_cosetWordBlock_0257
  · exact g32p_row13_cosetWordBlock_0258
  · exact g32p_row13_cosetWordBlock_0259
  · exact g32p_row13_cosetWordBlock_0260
  · exact g32p_row13_cosetWordBlock_0261
  · exact g32p_row13_cosetWordBlock_0262
  · exact g32p_row13_cosetWordBlock_0263
  · exact g32p_row13_cosetWordBlock_0264
  · exact g32p_row13_cosetWordBlock_0265
  · exact g32p_row13_cosetWordBlock_0266
  · exact g32p_row13_cosetWordBlock_0267
  · exact g32p_row13_cosetWordBlock_0268
  · exact g32p_row13_cosetWordBlock_0269
  · exact g32p_row13_cosetWordBlock_0270
  · exact g32p_row13_cosetWordBlock_0271
  · exact g32p_row13_cosetWordBlock_0272
  · exact g32p_row13_cosetWordBlock_0273
  · exact g32p_row13_cosetWordBlock_0274
  · exact g32p_row13_cosetWordBlock_0275
  · exact g32p_row13_cosetWordBlock_0276
  · exact g32p_row13_cosetWordBlock_0277
  · exact g32p_row13_cosetWordBlock_0278
  · exact g32p_row13_cosetWordBlock_0279
  · exact g32p_row13_cosetWordBlock_0280
  · exact g32p_row13_cosetWordBlock_0281
  · exact g32p_row13_cosetWordBlock_0282
  · exact g32p_row13_cosetWordBlock_0283
  · exact g32p_row13_cosetWordBlock_0284
  · exact g32p_row13_cosetWordBlock_0285
  · exact g32p_row13_cosetWordBlock_0286
  · exact g32p_row13_cosetWordBlock_0287
  · exact g32p_row13_cosetWordBlock_0288
  · exact g32p_row13_cosetWordBlock_0289
  · exact g32p_row13_cosetWordBlock_0290
  · exact g32p_row13_cosetWordBlock_0291
  · exact g32p_row13_cosetWordBlock_0292
  · exact g32p_row13_cosetWordBlock_0293
  · exact g32p_row13_cosetWordBlock_0294
  · exact g32p_row13_cosetWordBlock_0295
  · exact g32p_row13_cosetWordBlock_0296
  · exact g32p_row13_cosetWordBlock_0297
  · exact g32p_row13_cosetWordBlock_0298
  · exact g32p_row13_cosetWordBlock_0299
  · exact g32p_row13_cosetWordBlock_0300
  · exact g32p_row13_cosetWordBlock_0301
  · exact g32p_row13_cosetWordBlock_0302
  · exact g32p_row13_cosetWordBlock_0303
  · exact g32p_row13_cosetWordBlock_0304
  · exact g32p_row13_cosetWordBlock_0305
  · exact g32p_row13_cosetWordBlock_0306
  · exact g32p_row13_cosetWordBlock_0307
  · exact g32p_row13_cosetWordBlock_0308
  · exact g32p_row13_cosetWordBlock_0309
  · exact g32p_row13_cosetWordBlock_0310
  · exact g32p_row13_cosetWordBlock_0311
  · exact g32p_row13_cosetWordBlock_0312
  · exact g32p_row13_cosetWordBlock_0313
  · exact g32p_row13_cosetWordBlock_0314
  · exact g32p_row13_cosetWordBlock_0315
  · exact g32p_row13_cosetWordBlock_0316
  · exact g32p_row13_cosetWordBlock_0317
  · exact g32p_row13_cosetWordBlock_0318
  · exact g32p_row13_cosetWordBlock_0319
  · exact g32p_row13_cosetWordBlock_0320
  · exact g32p_row13_cosetWordBlock_0321
  · exact g32p_row13_cosetWordBlock_0322
  · exact g32p_row13_cosetWordBlock_0323
  · exact g32p_row13_cosetWordBlock_0324
  · exact g32p_row13_cosetWordBlock_0325
  · exact g32p_row13_cosetWordBlock_0326
  · exact g32p_row13_cosetWordBlock_0327
  · exact g32p_row13_cosetWordBlock_0328
  · exact g32p_row13_cosetWordBlock_0329
  · exact g32p_row13_cosetWordBlock_0330
  · exact g32p_row13_cosetWordBlock_0331
  · exact g32p_row13_cosetWordBlock_0332
  · exact g32p_row13_cosetWordBlock_0333
  · exact g32p_row13_cosetWordBlock_0334
  · exact g32p_row13_cosetWordBlock_0335
  · exact g32p_row13_cosetWordBlock_0336
  · exact g32p_row13_cosetWordBlock_0337
  · exact g32p_row13_cosetWordBlock_0338
  · exact g32p_row13_cosetWordBlock_0339
  · exact g32p_row13_cosetWordBlock_0340
  · exact g32p_row13_cosetWordBlock_0341
  · exact g32p_row13_cosetWordBlock_0342
  · exact g32p_row13_cosetWordBlock_0343
  · exact g32p_row13_cosetWordBlock_0344
  · exact g32p_row13_cosetWordBlock_0345
  · exact g32p_row13_cosetWordBlock_0346
  · exact g32p_row13_cosetWordBlock_0347
  · exact g32p_row13_cosetWordBlock_0348
  · exact g32p_row13_cosetWordBlock_0349
  · exact g32p_row13_cosetWordBlock_0350
  · exact g32p_row13_cosetWordBlock_0351
  · exact g32p_row13_cosetWordBlock_0352
  · exact g32p_row13_cosetWordBlock_0353
  · exact g32p_row13_cosetWordBlock_0354
  · exact g32p_row13_cosetWordBlock_0355
  · exact g32p_row13_cosetWordBlock_0356
  · exact g32p_row13_cosetWordBlock_0357
  · exact g32p_row13_cosetWordBlock_0358
  · exact g32p_row13_cosetWordBlock_0359
  · exact g32p_row13_cosetWordBlock_0360
  · exact g32p_row13_cosetWordBlock_0361
  · exact g32p_row13_cosetWordBlock_0362
  · exact g32p_row13_cosetWordBlock_0363
  · exact g32p_row13_cosetWordBlock_0364
  · exact g32p_row13_cosetWordBlock_0365
  · exact g32p_row13_cosetWordBlock_0366
  · exact g32p_row13_cosetWordBlock_0367
  · exact g32p_row13_cosetWordBlock_0368
  · exact g32p_row13_cosetWordBlock_0369
  · exact g32p_row13_cosetWordBlock_0370
  · exact g32p_row13_cosetWordBlock_0371
  · exact g32p_row13_cosetWordBlock_0372
  · exact g32p_row13_cosetWordBlock_0373
  · exact g32p_row13_cosetWordBlock_0374
  · exact g32p_row13_cosetWordBlock_0375
  · exact g32p_row13_cosetWordBlock_0376
  · exact g32p_row13_cosetWordBlock_0377
  · exact g32p_row13_cosetWordBlock_0378
  · exact g32p_row13_cosetWordBlock_0379
  · exact g32p_row13_cosetWordBlock_0380
  · exact g32p_row13_cosetWordBlock_0381
  · exact g32p_row13_cosetWordBlock_0382
  · exact g32p_row13_cosetWordBlock_0383
  · exact g32p_row13_cosetWordBlock_0384
  · exact g32p_row13_cosetWordBlock_0385
  · exact g32p_row13_cosetWordBlock_0386
  · exact g32p_row13_cosetWordBlock_0387
  · exact g32p_row13_cosetWordBlock_0388
  · exact g32p_row13_cosetWordBlock_0389
  · exact g32p_row13_cosetWordBlock_0390
  · exact g32p_row13_cosetWordBlock_0391
  · exact g32p_row13_cosetWordBlock_0392
  · exact g32p_row13_cosetWordBlock_0393
  · exact g32p_row13_cosetWordBlock_0394
  · exact g32p_row13_cosetWordBlock_0395
  · exact g32p_row13_cosetWordBlock_0396
  · exact g32p_row13_cosetWordBlock_0397
  · exact g32p_row13_cosetWordBlock_0398
  · exact g32p_row13_cosetWordBlock_0399
  · exact g32p_row13_cosetWordBlock_0400
  · exact g32p_row13_cosetWordBlock_0401
  · exact g32p_row13_cosetWordBlock_0402
  · exact g32p_row13_cosetWordBlock_0403
  · exact g32p_row13_cosetWordBlock_0404


def g32p_row13_cosetActualRepresentatives (i : Fin 6480) : g32p_G := g32p_archiveWord (g32p_row13_cosetWords i)

theorem g32p_row13_cosetActualRepresentatives_map (i : Fin 6480) :
    b4b_toMatrix (g32p_row13_cosetActualRepresentatives i) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row13_cosetRepresentatives i)) := by
  rw [g32p_row13_cosetActualRepresentatives, g32p_archiveIntegralWord_map, g32p_row13_cosetWord]

theorem g32p_row13_cosetGeneratorStep (s : Fin 4) (i : Fin 6480) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives i) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s i))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s i)) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row13_cosetGeneratorBlock_0000 s
  · exact g32p_row13_cosetGeneratorBlock_0001 s
  · exact g32p_row13_cosetGeneratorBlock_0002 s
  · exact g32p_row13_cosetGeneratorBlock_0003 s
  · exact g32p_row13_cosetGeneratorBlock_0004 s
  · exact g32p_row13_cosetGeneratorBlock_0005 s
  · exact g32p_row13_cosetGeneratorBlock_0006 s
  · exact g32p_row13_cosetGeneratorBlock_0007 s
  · exact g32p_row13_cosetGeneratorBlock_0008 s
  · exact g32p_row13_cosetGeneratorBlock_0009 s
  · exact g32p_row13_cosetGeneratorBlock_0010 s
  · exact g32p_row13_cosetGeneratorBlock_0011 s
  · exact g32p_row13_cosetGeneratorBlock_0012 s
  · exact g32p_row13_cosetGeneratorBlock_0013 s
  · exact g32p_row13_cosetGeneratorBlock_0014 s
  · exact g32p_row13_cosetGeneratorBlock_0015 s
  · exact g32p_row13_cosetGeneratorBlock_0016 s
  · exact g32p_row13_cosetGeneratorBlock_0017 s
  · exact g32p_row13_cosetGeneratorBlock_0018 s
  · exact g32p_row13_cosetGeneratorBlock_0019 s
  · exact g32p_row13_cosetGeneratorBlock_0020 s
  · exact g32p_row13_cosetGeneratorBlock_0021 s
  · exact g32p_row13_cosetGeneratorBlock_0022 s
  · exact g32p_row13_cosetGeneratorBlock_0023 s
  · exact g32p_row13_cosetGeneratorBlock_0024 s
  · exact g32p_row13_cosetGeneratorBlock_0025 s
  · exact g32p_row13_cosetGeneratorBlock_0026 s
  · exact g32p_row13_cosetGeneratorBlock_0027 s
  · exact g32p_row13_cosetGeneratorBlock_0028 s
  · exact g32p_row13_cosetGeneratorBlock_0029 s
  · exact g32p_row13_cosetGeneratorBlock_0030 s
  · exact g32p_row13_cosetGeneratorBlock_0031 s
  · exact g32p_row13_cosetGeneratorBlock_0032 s
  · exact g32p_row13_cosetGeneratorBlock_0033 s
  · exact g32p_row13_cosetGeneratorBlock_0034 s
  · exact g32p_row13_cosetGeneratorBlock_0035 s
  · exact g32p_row13_cosetGeneratorBlock_0036 s
  · exact g32p_row13_cosetGeneratorBlock_0037 s
  · exact g32p_row13_cosetGeneratorBlock_0038 s
  · exact g32p_row13_cosetGeneratorBlock_0039 s
  · exact g32p_row13_cosetGeneratorBlock_0040 s
  · exact g32p_row13_cosetGeneratorBlock_0041 s
  · exact g32p_row13_cosetGeneratorBlock_0042 s
  · exact g32p_row13_cosetGeneratorBlock_0043 s
  · exact g32p_row13_cosetGeneratorBlock_0044 s
  · exact g32p_row13_cosetGeneratorBlock_0045 s
  · exact g32p_row13_cosetGeneratorBlock_0046 s
  · exact g32p_row13_cosetGeneratorBlock_0047 s
  · exact g32p_row13_cosetGeneratorBlock_0048 s
  · exact g32p_row13_cosetGeneratorBlock_0049 s
  · exact g32p_row13_cosetGeneratorBlock_0050 s
  · exact g32p_row13_cosetGeneratorBlock_0051 s
  · exact g32p_row13_cosetGeneratorBlock_0052 s
  · exact g32p_row13_cosetGeneratorBlock_0053 s
  · exact g32p_row13_cosetGeneratorBlock_0054 s
  · exact g32p_row13_cosetGeneratorBlock_0055 s
  · exact g32p_row13_cosetGeneratorBlock_0056 s
  · exact g32p_row13_cosetGeneratorBlock_0057 s
  · exact g32p_row13_cosetGeneratorBlock_0058 s
  · exact g32p_row13_cosetGeneratorBlock_0059 s
  · exact g32p_row13_cosetGeneratorBlock_0060 s
  · exact g32p_row13_cosetGeneratorBlock_0061 s
  · exact g32p_row13_cosetGeneratorBlock_0062 s
  · exact g32p_row13_cosetGeneratorBlock_0063 s
  · exact g32p_row13_cosetGeneratorBlock_0064 s
  · exact g32p_row13_cosetGeneratorBlock_0065 s
  · exact g32p_row13_cosetGeneratorBlock_0066 s
  · exact g32p_row13_cosetGeneratorBlock_0067 s
  · exact g32p_row13_cosetGeneratorBlock_0068 s
  · exact g32p_row13_cosetGeneratorBlock_0069 s
  · exact g32p_row13_cosetGeneratorBlock_0070 s
  · exact g32p_row13_cosetGeneratorBlock_0071 s
  · exact g32p_row13_cosetGeneratorBlock_0072 s
  · exact g32p_row13_cosetGeneratorBlock_0073 s
  · exact g32p_row13_cosetGeneratorBlock_0074 s
  · exact g32p_row13_cosetGeneratorBlock_0075 s
  · exact g32p_row13_cosetGeneratorBlock_0076 s
  · exact g32p_row13_cosetGeneratorBlock_0077 s
  · exact g32p_row13_cosetGeneratorBlock_0078 s
  · exact g32p_row13_cosetGeneratorBlock_0079 s
  · exact g32p_row13_cosetGeneratorBlock_0080 s
  · exact g32p_row13_cosetGeneratorBlock_0081 s
  · exact g32p_row13_cosetGeneratorBlock_0082 s
  · exact g32p_row13_cosetGeneratorBlock_0083 s
  · exact g32p_row13_cosetGeneratorBlock_0084 s
  · exact g32p_row13_cosetGeneratorBlock_0085 s
  · exact g32p_row13_cosetGeneratorBlock_0086 s
  · exact g32p_row13_cosetGeneratorBlock_0087 s
  · exact g32p_row13_cosetGeneratorBlock_0088 s
  · exact g32p_row13_cosetGeneratorBlock_0089 s
  · exact g32p_row13_cosetGeneratorBlock_0090 s
  · exact g32p_row13_cosetGeneratorBlock_0091 s
  · exact g32p_row13_cosetGeneratorBlock_0092 s
  · exact g32p_row13_cosetGeneratorBlock_0093 s
  · exact g32p_row13_cosetGeneratorBlock_0094 s
  · exact g32p_row13_cosetGeneratorBlock_0095 s
  · exact g32p_row13_cosetGeneratorBlock_0096 s
  · exact g32p_row13_cosetGeneratorBlock_0097 s
  · exact g32p_row13_cosetGeneratorBlock_0098 s
  · exact g32p_row13_cosetGeneratorBlock_0099 s
  · exact g32p_row13_cosetGeneratorBlock_0100 s
  · exact g32p_row13_cosetGeneratorBlock_0101 s
  · exact g32p_row13_cosetGeneratorBlock_0102 s
  · exact g32p_row13_cosetGeneratorBlock_0103 s
  · exact g32p_row13_cosetGeneratorBlock_0104 s
  · exact g32p_row13_cosetGeneratorBlock_0105 s
  · exact g32p_row13_cosetGeneratorBlock_0106 s
  · exact g32p_row13_cosetGeneratorBlock_0107 s
  · exact g32p_row13_cosetGeneratorBlock_0108 s
  · exact g32p_row13_cosetGeneratorBlock_0109 s
  · exact g32p_row13_cosetGeneratorBlock_0110 s
  · exact g32p_row13_cosetGeneratorBlock_0111 s
  · exact g32p_row13_cosetGeneratorBlock_0112 s
  · exact g32p_row13_cosetGeneratorBlock_0113 s
  · exact g32p_row13_cosetGeneratorBlock_0114 s
  · exact g32p_row13_cosetGeneratorBlock_0115 s
  · exact g32p_row13_cosetGeneratorBlock_0116 s
  · exact g32p_row13_cosetGeneratorBlock_0117 s
  · exact g32p_row13_cosetGeneratorBlock_0118 s
  · exact g32p_row13_cosetGeneratorBlock_0119 s
  · exact g32p_row13_cosetGeneratorBlock_0120 s
  · exact g32p_row13_cosetGeneratorBlock_0121 s
  · exact g32p_row13_cosetGeneratorBlock_0122 s
  · exact g32p_row13_cosetGeneratorBlock_0123 s
  · exact g32p_row13_cosetGeneratorBlock_0124 s
  · exact g32p_row13_cosetGeneratorBlock_0125 s
  · exact g32p_row13_cosetGeneratorBlock_0126 s
  · exact g32p_row13_cosetGeneratorBlock_0127 s
  · exact g32p_row13_cosetGeneratorBlock_0128 s
  · exact g32p_row13_cosetGeneratorBlock_0129 s
  · exact g32p_row13_cosetGeneratorBlock_0130 s
  · exact g32p_row13_cosetGeneratorBlock_0131 s
  · exact g32p_row13_cosetGeneratorBlock_0132 s
  · exact g32p_row13_cosetGeneratorBlock_0133 s
  · exact g32p_row13_cosetGeneratorBlock_0134 s
  · exact g32p_row13_cosetGeneratorBlock_0135 s
  · exact g32p_row13_cosetGeneratorBlock_0136 s
  · exact g32p_row13_cosetGeneratorBlock_0137 s
  · exact g32p_row13_cosetGeneratorBlock_0138 s
  · exact g32p_row13_cosetGeneratorBlock_0139 s
  · exact g32p_row13_cosetGeneratorBlock_0140 s
  · exact g32p_row13_cosetGeneratorBlock_0141 s
  · exact g32p_row13_cosetGeneratorBlock_0142 s
  · exact g32p_row13_cosetGeneratorBlock_0143 s
  · exact g32p_row13_cosetGeneratorBlock_0144 s
  · exact g32p_row13_cosetGeneratorBlock_0145 s
  · exact g32p_row13_cosetGeneratorBlock_0146 s
  · exact g32p_row13_cosetGeneratorBlock_0147 s
  · exact g32p_row13_cosetGeneratorBlock_0148 s
  · exact g32p_row13_cosetGeneratorBlock_0149 s
  · exact g32p_row13_cosetGeneratorBlock_0150 s
  · exact g32p_row13_cosetGeneratorBlock_0151 s
  · exact g32p_row13_cosetGeneratorBlock_0152 s
  · exact g32p_row13_cosetGeneratorBlock_0153 s
  · exact g32p_row13_cosetGeneratorBlock_0154 s
  · exact g32p_row13_cosetGeneratorBlock_0155 s
  · exact g32p_row13_cosetGeneratorBlock_0156 s
  · exact g32p_row13_cosetGeneratorBlock_0157 s
  · exact g32p_row13_cosetGeneratorBlock_0158 s
  · exact g32p_row13_cosetGeneratorBlock_0159 s
  · exact g32p_row13_cosetGeneratorBlock_0160 s
  · exact g32p_row13_cosetGeneratorBlock_0161 s
  · exact g32p_row13_cosetGeneratorBlock_0162 s
  · exact g32p_row13_cosetGeneratorBlock_0163 s
  · exact g32p_row13_cosetGeneratorBlock_0164 s
  · exact g32p_row13_cosetGeneratorBlock_0165 s
  · exact g32p_row13_cosetGeneratorBlock_0166 s
  · exact g32p_row13_cosetGeneratorBlock_0167 s
  · exact g32p_row13_cosetGeneratorBlock_0168 s
  · exact g32p_row13_cosetGeneratorBlock_0169 s
  · exact g32p_row13_cosetGeneratorBlock_0170 s
  · exact g32p_row13_cosetGeneratorBlock_0171 s
  · exact g32p_row13_cosetGeneratorBlock_0172 s
  · exact g32p_row13_cosetGeneratorBlock_0173 s
  · exact g32p_row13_cosetGeneratorBlock_0174 s
  · exact g32p_row13_cosetGeneratorBlock_0175 s
  · exact g32p_row13_cosetGeneratorBlock_0176 s
  · exact g32p_row13_cosetGeneratorBlock_0177 s
  · exact g32p_row13_cosetGeneratorBlock_0178 s
  · exact g32p_row13_cosetGeneratorBlock_0179 s
  · exact g32p_row13_cosetGeneratorBlock_0180 s
  · exact g32p_row13_cosetGeneratorBlock_0181 s
  · exact g32p_row13_cosetGeneratorBlock_0182 s
  · exact g32p_row13_cosetGeneratorBlock_0183 s
  · exact g32p_row13_cosetGeneratorBlock_0184 s
  · exact g32p_row13_cosetGeneratorBlock_0185 s
  · exact g32p_row13_cosetGeneratorBlock_0186 s
  · exact g32p_row13_cosetGeneratorBlock_0187 s
  · exact g32p_row13_cosetGeneratorBlock_0188 s
  · exact g32p_row13_cosetGeneratorBlock_0189 s
  · exact g32p_row13_cosetGeneratorBlock_0190 s
  · exact g32p_row13_cosetGeneratorBlock_0191 s
  · exact g32p_row13_cosetGeneratorBlock_0192 s
  · exact g32p_row13_cosetGeneratorBlock_0193 s
  · exact g32p_row13_cosetGeneratorBlock_0194 s
  · exact g32p_row13_cosetGeneratorBlock_0195 s
  · exact g32p_row13_cosetGeneratorBlock_0196 s
  · exact g32p_row13_cosetGeneratorBlock_0197 s
  · exact g32p_row13_cosetGeneratorBlock_0198 s
  · exact g32p_row13_cosetGeneratorBlock_0199 s
  · exact g32p_row13_cosetGeneratorBlock_0200 s
  · exact g32p_row13_cosetGeneratorBlock_0201 s
  · exact g32p_row13_cosetGeneratorBlock_0202 s
  · exact g32p_row13_cosetGeneratorBlock_0203 s
  · exact g32p_row13_cosetGeneratorBlock_0204 s
  · exact g32p_row13_cosetGeneratorBlock_0205 s
  · exact g32p_row13_cosetGeneratorBlock_0206 s
  · exact g32p_row13_cosetGeneratorBlock_0207 s
  · exact g32p_row13_cosetGeneratorBlock_0208 s
  · exact g32p_row13_cosetGeneratorBlock_0209 s
  · exact g32p_row13_cosetGeneratorBlock_0210 s
  · exact g32p_row13_cosetGeneratorBlock_0211 s
  · exact g32p_row13_cosetGeneratorBlock_0212 s
  · exact g32p_row13_cosetGeneratorBlock_0213 s
  · exact g32p_row13_cosetGeneratorBlock_0214 s
  · exact g32p_row13_cosetGeneratorBlock_0215 s
  · exact g32p_row13_cosetGeneratorBlock_0216 s
  · exact g32p_row13_cosetGeneratorBlock_0217 s
  · exact g32p_row13_cosetGeneratorBlock_0218 s
  · exact g32p_row13_cosetGeneratorBlock_0219 s
  · exact g32p_row13_cosetGeneratorBlock_0220 s
  · exact g32p_row13_cosetGeneratorBlock_0221 s
  · exact g32p_row13_cosetGeneratorBlock_0222 s
  · exact g32p_row13_cosetGeneratorBlock_0223 s
  · exact g32p_row13_cosetGeneratorBlock_0224 s
  · exact g32p_row13_cosetGeneratorBlock_0225 s
  · exact g32p_row13_cosetGeneratorBlock_0226 s
  · exact g32p_row13_cosetGeneratorBlock_0227 s
  · exact g32p_row13_cosetGeneratorBlock_0228 s
  · exact g32p_row13_cosetGeneratorBlock_0229 s
  · exact g32p_row13_cosetGeneratorBlock_0230 s
  · exact g32p_row13_cosetGeneratorBlock_0231 s
  · exact g32p_row13_cosetGeneratorBlock_0232 s
  · exact g32p_row13_cosetGeneratorBlock_0233 s
  · exact g32p_row13_cosetGeneratorBlock_0234 s
  · exact g32p_row13_cosetGeneratorBlock_0235 s
  · exact g32p_row13_cosetGeneratorBlock_0236 s
  · exact g32p_row13_cosetGeneratorBlock_0237 s
  · exact g32p_row13_cosetGeneratorBlock_0238 s
  · exact g32p_row13_cosetGeneratorBlock_0239 s
  · exact g32p_row13_cosetGeneratorBlock_0240 s
  · exact g32p_row13_cosetGeneratorBlock_0241 s
  · exact g32p_row13_cosetGeneratorBlock_0242 s
  · exact g32p_row13_cosetGeneratorBlock_0243 s
  · exact g32p_row13_cosetGeneratorBlock_0244 s
  · exact g32p_row13_cosetGeneratorBlock_0245 s
  · exact g32p_row13_cosetGeneratorBlock_0246 s
  · exact g32p_row13_cosetGeneratorBlock_0247 s
  · exact g32p_row13_cosetGeneratorBlock_0248 s
  · exact g32p_row13_cosetGeneratorBlock_0249 s
  · exact g32p_row13_cosetGeneratorBlock_0250 s
  · exact g32p_row13_cosetGeneratorBlock_0251 s
  · exact g32p_row13_cosetGeneratorBlock_0252 s
  · exact g32p_row13_cosetGeneratorBlock_0253 s
  · exact g32p_row13_cosetGeneratorBlock_0254 s
  · exact g32p_row13_cosetGeneratorBlock_0255 s
  · exact g32p_row13_cosetGeneratorBlock_0256 s
  · exact g32p_row13_cosetGeneratorBlock_0257 s
  · exact g32p_row13_cosetGeneratorBlock_0258 s
  · exact g32p_row13_cosetGeneratorBlock_0259 s
  · exact g32p_row13_cosetGeneratorBlock_0260 s
  · exact g32p_row13_cosetGeneratorBlock_0261 s
  · exact g32p_row13_cosetGeneratorBlock_0262 s
  · exact g32p_row13_cosetGeneratorBlock_0263 s
  · exact g32p_row13_cosetGeneratorBlock_0264 s
  · exact g32p_row13_cosetGeneratorBlock_0265 s
  · exact g32p_row13_cosetGeneratorBlock_0266 s
  · exact g32p_row13_cosetGeneratorBlock_0267 s
  · exact g32p_row13_cosetGeneratorBlock_0268 s
  · exact g32p_row13_cosetGeneratorBlock_0269 s
  · exact g32p_row13_cosetGeneratorBlock_0270 s
  · exact g32p_row13_cosetGeneratorBlock_0271 s
  · exact g32p_row13_cosetGeneratorBlock_0272 s
  · exact g32p_row13_cosetGeneratorBlock_0273 s
  · exact g32p_row13_cosetGeneratorBlock_0274 s
  · exact g32p_row13_cosetGeneratorBlock_0275 s
  · exact g32p_row13_cosetGeneratorBlock_0276 s
  · exact g32p_row13_cosetGeneratorBlock_0277 s
  · exact g32p_row13_cosetGeneratorBlock_0278 s
  · exact g32p_row13_cosetGeneratorBlock_0279 s
  · exact g32p_row13_cosetGeneratorBlock_0280 s
  · exact g32p_row13_cosetGeneratorBlock_0281 s
  · exact g32p_row13_cosetGeneratorBlock_0282 s
  · exact g32p_row13_cosetGeneratorBlock_0283 s
  · exact g32p_row13_cosetGeneratorBlock_0284 s
  · exact g32p_row13_cosetGeneratorBlock_0285 s
  · exact g32p_row13_cosetGeneratorBlock_0286 s
  · exact g32p_row13_cosetGeneratorBlock_0287 s
  · exact g32p_row13_cosetGeneratorBlock_0288 s
  · exact g32p_row13_cosetGeneratorBlock_0289 s
  · exact g32p_row13_cosetGeneratorBlock_0290 s
  · exact g32p_row13_cosetGeneratorBlock_0291 s
  · exact g32p_row13_cosetGeneratorBlock_0292 s
  · exact g32p_row13_cosetGeneratorBlock_0293 s
  · exact g32p_row13_cosetGeneratorBlock_0294 s
  · exact g32p_row13_cosetGeneratorBlock_0295 s
  · exact g32p_row13_cosetGeneratorBlock_0296 s
  · exact g32p_row13_cosetGeneratorBlock_0297 s
  · exact g32p_row13_cosetGeneratorBlock_0298 s
  · exact g32p_row13_cosetGeneratorBlock_0299 s
  · exact g32p_row13_cosetGeneratorBlock_0300 s
  · exact g32p_row13_cosetGeneratorBlock_0301 s
  · exact g32p_row13_cosetGeneratorBlock_0302 s
  · exact g32p_row13_cosetGeneratorBlock_0303 s
  · exact g32p_row13_cosetGeneratorBlock_0304 s
  · exact g32p_row13_cosetGeneratorBlock_0305 s
  · exact g32p_row13_cosetGeneratorBlock_0306 s
  · exact g32p_row13_cosetGeneratorBlock_0307 s
  · exact g32p_row13_cosetGeneratorBlock_0308 s
  · exact g32p_row13_cosetGeneratorBlock_0309 s
  · exact g32p_row13_cosetGeneratorBlock_0310 s
  · exact g32p_row13_cosetGeneratorBlock_0311 s
  · exact g32p_row13_cosetGeneratorBlock_0312 s
  · exact g32p_row13_cosetGeneratorBlock_0313 s
  · exact g32p_row13_cosetGeneratorBlock_0314 s
  · exact g32p_row13_cosetGeneratorBlock_0315 s
  · exact g32p_row13_cosetGeneratorBlock_0316 s
  · exact g32p_row13_cosetGeneratorBlock_0317 s
  · exact g32p_row13_cosetGeneratorBlock_0318 s
  · exact g32p_row13_cosetGeneratorBlock_0319 s
  · exact g32p_row13_cosetGeneratorBlock_0320 s
  · exact g32p_row13_cosetGeneratorBlock_0321 s
  · exact g32p_row13_cosetGeneratorBlock_0322 s
  · exact g32p_row13_cosetGeneratorBlock_0323 s
  · exact g32p_row13_cosetGeneratorBlock_0324 s
  · exact g32p_row13_cosetGeneratorBlock_0325 s
  · exact g32p_row13_cosetGeneratorBlock_0326 s
  · exact g32p_row13_cosetGeneratorBlock_0327 s
  · exact g32p_row13_cosetGeneratorBlock_0328 s
  · exact g32p_row13_cosetGeneratorBlock_0329 s
  · exact g32p_row13_cosetGeneratorBlock_0330 s
  · exact g32p_row13_cosetGeneratorBlock_0331 s
  · exact g32p_row13_cosetGeneratorBlock_0332 s
  · exact g32p_row13_cosetGeneratorBlock_0333 s
  · exact g32p_row13_cosetGeneratorBlock_0334 s
  · exact g32p_row13_cosetGeneratorBlock_0335 s
  · exact g32p_row13_cosetGeneratorBlock_0336 s
  · exact g32p_row13_cosetGeneratorBlock_0337 s
  · exact g32p_row13_cosetGeneratorBlock_0338 s
  · exact g32p_row13_cosetGeneratorBlock_0339 s
  · exact g32p_row13_cosetGeneratorBlock_0340 s
  · exact g32p_row13_cosetGeneratorBlock_0341 s
  · exact g32p_row13_cosetGeneratorBlock_0342 s
  · exact g32p_row13_cosetGeneratorBlock_0343 s
  · exact g32p_row13_cosetGeneratorBlock_0344 s
  · exact g32p_row13_cosetGeneratorBlock_0345 s
  · exact g32p_row13_cosetGeneratorBlock_0346 s
  · exact g32p_row13_cosetGeneratorBlock_0347 s
  · exact g32p_row13_cosetGeneratorBlock_0348 s
  · exact g32p_row13_cosetGeneratorBlock_0349 s
  · exact g32p_row13_cosetGeneratorBlock_0350 s
  · exact g32p_row13_cosetGeneratorBlock_0351 s
  · exact g32p_row13_cosetGeneratorBlock_0352 s
  · exact g32p_row13_cosetGeneratorBlock_0353 s
  · exact g32p_row13_cosetGeneratorBlock_0354 s
  · exact g32p_row13_cosetGeneratorBlock_0355 s
  · exact g32p_row13_cosetGeneratorBlock_0356 s
  · exact g32p_row13_cosetGeneratorBlock_0357 s
  · exact g32p_row13_cosetGeneratorBlock_0358 s
  · exact g32p_row13_cosetGeneratorBlock_0359 s
  · exact g32p_row13_cosetGeneratorBlock_0360 s
  · exact g32p_row13_cosetGeneratorBlock_0361 s
  · exact g32p_row13_cosetGeneratorBlock_0362 s
  · exact g32p_row13_cosetGeneratorBlock_0363 s
  · exact g32p_row13_cosetGeneratorBlock_0364 s
  · exact g32p_row13_cosetGeneratorBlock_0365 s
  · exact g32p_row13_cosetGeneratorBlock_0366 s
  · exact g32p_row13_cosetGeneratorBlock_0367 s
  · exact g32p_row13_cosetGeneratorBlock_0368 s
  · exact g32p_row13_cosetGeneratorBlock_0369 s
  · exact g32p_row13_cosetGeneratorBlock_0370 s
  · exact g32p_row13_cosetGeneratorBlock_0371 s
  · exact g32p_row13_cosetGeneratorBlock_0372 s
  · exact g32p_row13_cosetGeneratorBlock_0373 s
  · exact g32p_row13_cosetGeneratorBlock_0374 s
  · exact g32p_row13_cosetGeneratorBlock_0375 s
  · exact g32p_row13_cosetGeneratorBlock_0376 s
  · exact g32p_row13_cosetGeneratorBlock_0377 s
  · exact g32p_row13_cosetGeneratorBlock_0378 s
  · exact g32p_row13_cosetGeneratorBlock_0379 s
  · exact g32p_row13_cosetGeneratorBlock_0380 s
  · exact g32p_row13_cosetGeneratorBlock_0381 s
  · exact g32p_row13_cosetGeneratorBlock_0382 s
  · exact g32p_row13_cosetGeneratorBlock_0383 s
  · exact g32p_row13_cosetGeneratorBlock_0384 s
  · exact g32p_row13_cosetGeneratorBlock_0385 s
  · exact g32p_row13_cosetGeneratorBlock_0386 s
  · exact g32p_row13_cosetGeneratorBlock_0387 s
  · exact g32p_row13_cosetGeneratorBlock_0388 s
  · exact g32p_row13_cosetGeneratorBlock_0389 s
  · exact g32p_row13_cosetGeneratorBlock_0390 s
  · exact g32p_row13_cosetGeneratorBlock_0391 s
  · exact g32p_row13_cosetGeneratorBlock_0392 s
  · exact g32p_row13_cosetGeneratorBlock_0393 s
  · exact g32p_row13_cosetGeneratorBlock_0394 s
  · exact g32p_row13_cosetGeneratorBlock_0395 s
  · exact g32p_row13_cosetGeneratorBlock_0396 s
  · exact g32p_row13_cosetGeneratorBlock_0397 s
  · exact g32p_row13_cosetGeneratorBlock_0398 s
  · exact g32p_row13_cosetGeneratorBlock_0399 s
  · exact g32p_row13_cosetGeneratorBlock_0400 s
  · exact g32p_row13_cosetGeneratorBlock_0401 s
  · exact g32p_row13_cosetGeneratorBlock_0402 s
  · exact g32p_row13_cosetGeneratorBlock_0403 s
  · exact g32p_row13_cosetGeneratorBlock_0404 s


theorem g32p_row13_cosetActualStep (s : Fin 4) (i : Fin 6480) :
    g32p_word (g32p_archiveWords s) * g32p_row13_cosetActualRepresentatives i =
      g32p_row13_cosetActualRepresentatives (g32p_row13_cosetGeneratorNext s i) *
        (g32p_row13_groupEquiv (g32p_row13_cosetGeneratorFactor s i) : g32p_G) := by
  apply Subtype.ext
  change b4b_toMatrix (g32p_word (g32p_archiveWords s) * g32p_row13_cosetActualRepresentatives i) =
    b4b_toMatrix (g32p_row13_cosetActualRepresentatives (g32p_row13_cosetGeneratorNext s i) *
      (g32p_row13_groupEquiv (g32p_row13_cosetGeneratorFactor s i) : g32p_G))
  rw [map_mul, map_mul, g32p_row13_cosetActualRepresentatives_map,
    g32p_row13_cosetActualRepresentatives_map, g32p_row13_groupEquiv_map,
    g32p_integralWord_map, g32p_archiveWordIntegral,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    g32p_row13_cosetGeneratorStep]

theorem g32p_row13_cosetEnumeration :
    Function.Bijective (fun i => (QuotientGroup.mk (g32p_row13_cosetActualRepresentatives i) :
      g32p_G ⧸ g32p_row13_finiteSupplier.H)) := by
  apply g32p_coset_bijective
  · apply g32p_coset_surjective _ _ g32p_archive_generators_top _ 0 (by rfl)
      g32p_row13_cosetGeneratorNext
      (fun s i => g32p_row13_groupEquiv (g32p_row13_cosetGeneratorFactor s i))
    exact g32p_row13_cosetActualStep
  · rw [g32p_row13_finiteSupplier_order]
    have hg : Nat.card g32p_G = 155520 :=
      (Nat.card_coe_set_eq (g32h_G : Set (Matrix (Fin 4) (Fin 4) ℂ))).trans
        HurwitzPrymRex_g32_ncard
    rw [hg]


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_cosetBranchCheck (b : Fin 3) (i : Fin 6480) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices b) (g32p_row13_cosetRepresentatives i) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext b i))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor b i)) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row13_cosetBranchBlock_0000 b
  · exact g32p_row13_cosetBranchBlock_0001 b
  · exact g32p_row13_cosetBranchBlock_0002 b
  · exact g32p_row13_cosetBranchBlock_0003 b
  · exact g32p_row13_cosetBranchBlock_0004 b
  · exact g32p_row13_cosetBranchBlock_0005 b
  · exact g32p_row13_cosetBranchBlock_0006 b
  · exact g32p_row13_cosetBranchBlock_0007 b
  · exact g32p_row13_cosetBranchBlock_0008 b
  · exact g32p_row13_cosetBranchBlock_0009 b
  · exact g32p_row13_cosetBranchBlock_0010 b
  · exact g32p_row13_cosetBranchBlock_0011 b
  · exact g32p_row13_cosetBranchBlock_0012 b
  · exact g32p_row13_cosetBranchBlock_0013 b
  · exact g32p_row13_cosetBranchBlock_0014 b
  · exact g32p_row13_cosetBranchBlock_0015 b
  · exact g32p_row13_cosetBranchBlock_0016 b
  · exact g32p_row13_cosetBranchBlock_0017 b
  · exact g32p_row13_cosetBranchBlock_0018 b
  · exact g32p_row13_cosetBranchBlock_0019 b
  · exact g32p_row13_cosetBranchBlock_0020 b
  · exact g32p_row13_cosetBranchBlock_0021 b
  · exact g32p_row13_cosetBranchBlock_0022 b
  · exact g32p_row13_cosetBranchBlock_0023 b
  · exact g32p_row13_cosetBranchBlock_0024 b
  · exact g32p_row13_cosetBranchBlock_0025 b
  · exact g32p_row13_cosetBranchBlock_0026 b
  · exact g32p_row13_cosetBranchBlock_0027 b
  · exact g32p_row13_cosetBranchBlock_0028 b
  · exact g32p_row13_cosetBranchBlock_0029 b
  · exact g32p_row13_cosetBranchBlock_0030 b
  · exact g32p_row13_cosetBranchBlock_0031 b
  · exact g32p_row13_cosetBranchBlock_0032 b
  · exact g32p_row13_cosetBranchBlock_0033 b
  · exact g32p_row13_cosetBranchBlock_0034 b
  · exact g32p_row13_cosetBranchBlock_0035 b
  · exact g32p_row13_cosetBranchBlock_0036 b
  · exact g32p_row13_cosetBranchBlock_0037 b
  · exact g32p_row13_cosetBranchBlock_0038 b
  · exact g32p_row13_cosetBranchBlock_0039 b
  · exact g32p_row13_cosetBranchBlock_0040 b
  · exact g32p_row13_cosetBranchBlock_0041 b
  · exact g32p_row13_cosetBranchBlock_0042 b
  · exact g32p_row13_cosetBranchBlock_0043 b
  · exact g32p_row13_cosetBranchBlock_0044 b
  · exact g32p_row13_cosetBranchBlock_0045 b
  · exact g32p_row13_cosetBranchBlock_0046 b
  · exact g32p_row13_cosetBranchBlock_0047 b
  · exact g32p_row13_cosetBranchBlock_0048 b
  · exact g32p_row13_cosetBranchBlock_0049 b
  · exact g32p_row13_cosetBranchBlock_0050 b
  · exact g32p_row13_cosetBranchBlock_0051 b
  · exact g32p_row13_cosetBranchBlock_0052 b
  · exact g32p_row13_cosetBranchBlock_0053 b
  · exact g32p_row13_cosetBranchBlock_0054 b
  · exact g32p_row13_cosetBranchBlock_0055 b
  · exact g32p_row13_cosetBranchBlock_0056 b
  · exact g32p_row13_cosetBranchBlock_0057 b
  · exact g32p_row13_cosetBranchBlock_0058 b
  · exact g32p_row13_cosetBranchBlock_0059 b
  · exact g32p_row13_cosetBranchBlock_0060 b
  · exact g32p_row13_cosetBranchBlock_0061 b
  · exact g32p_row13_cosetBranchBlock_0062 b
  · exact g32p_row13_cosetBranchBlock_0063 b
  · exact g32p_row13_cosetBranchBlock_0064 b
  · exact g32p_row13_cosetBranchBlock_0065 b
  · exact g32p_row13_cosetBranchBlock_0066 b
  · exact g32p_row13_cosetBranchBlock_0067 b
  · exact g32p_row13_cosetBranchBlock_0068 b
  · exact g32p_row13_cosetBranchBlock_0069 b
  · exact g32p_row13_cosetBranchBlock_0070 b
  · exact g32p_row13_cosetBranchBlock_0071 b
  · exact g32p_row13_cosetBranchBlock_0072 b
  · exact g32p_row13_cosetBranchBlock_0073 b
  · exact g32p_row13_cosetBranchBlock_0074 b
  · exact g32p_row13_cosetBranchBlock_0075 b
  · exact g32p_row13_cosetBranchBlock_0076 b
  · exact g32p_row13_cosetBranchBlock_0077 b
  · exact g32p_row13_cosetBranchBlock_0078 b
  · exact g32p_row13_cosetBranchBlock_0079 b
  · exact g32p_row13_cosetBranchBlock_0080 b
  · exact g32p_row13_cosetBranchBlock_0081 b
  · exact g32p_row13_cosetBranchBlock_0082 b
  · exact g32p_row13_cosetBranchBlock_0083 b
  · exact g32p_row13_cosetBranchBlock_0084 b
  · exact g32p_row13_cosetBranchBlock_0085 b
  · exact g32p_row13_cosetBranchBlock_0086 b
  · exact g32p_row13_cosetBranchBlock_0087 b
  · exact g32p_row13_cosetBranchBlock_0088 b
  · exact g32p_row13_cosetBranchBlock_0089 b
  · exact g32p_row13_cosetBranchBlock_0090 b
  · exact g32p_row13_cosetBranchBlock_0091 b
  · exact g32p_row13_cosetBranchBlock_0092 b
  · exact g32p_row13_cosetBranchBlock_0093 b
  · exact g32p_row13_cosetBranchBlock_0094 b
  · exact g32p_row13_cosetBranchBlock_0095 b
  · exact g32p_row13_cosetBranchBlock_0096 b
  · exact g32p_row13_cosetBranchBlock_0097 b
  · exact g32p_row13_cosetBranchBlock_0098 b
  · exact g32p_row13_cosetBranchBlock_0099 b
  · exact g32p_row13_cosetBranchBlock_0100 b
  · exact g32p_row13_cosetBranchBlock_0101 b
  · exact g32p_row13_cosetBranchBlock_0102 b
  · exact g32p_row13_cosetBranchBlock_0103 b
  · exact g32p_row13_cosetBranchBlock_0104 b
  · exact g32p_row13_cosetBranchBlock_0105 b
  · exact g32p_row13_cosetBranchBlock_0106 b
  · exact g32p_row13_cosetBranchBlock_0107 b
  · exact g32p_row13_cosetBranchBlock_0108 b
  · exact g32p_row13_cosetBranchBlock_0109 b
  · exact g32p_row13_cosetBranchBlock_0110 b
  · exact g32p_row13_cosetBranchBlock_0111 b
  · exact g32p_row13_cosetBranchBlock_0112 b
  · exact g32p_row13_cosetBranchBlock_0113 b
  · exact g32p_row13_cosetBranchBlock_0114 b
  · exact g32p_row13_cosetBranchBlock_0115 b
  · exact g32p_row13_cosetBranchBlock_0116 b
  · exact g32p_row13_cosetBranchBlock_0117 b
  · exact g32p_row13_cosetBranchBlock_0118 b
  · exact g32p_row13_cosetBranchBlock_0119 b
  · exact g32p_row13_cosetBranchBlock_0120 b
  · exact g32p_row13_cosetBranchBlock_0121 b
  · exact g32p_row13_cosetBranchBlock_0122 b
  · exact g32p_row13_cosetBranchBlock_0123 b
  · exact g32p_row13_cosetBranchBlock_0124 b
  · exact g32p_row13_cosetBranchBlock_0125 b
  · exact g32p_row13_cosetBranchBlock_0126 b
  · exact g32p_row13_cosetBranchBlock_0127 b
  · exact g32p_row13_cosetBranchBlock_0128 b
  · exact g32p_row13_cosetBranchBlock_0129 b
  · exact g32p_row13_cosetBranchBlock_0130 b
  · exact g32p_row13_cosetBranchBlock_0131 b
  · exact g32p_row13_cosetBranchBlock_0132 b
  · exact g32p_row13_cosetBranchBlock_0133 b
  · exact g32p_row13_cosetBranchBlock_0134 b
  · exact g32p_row13_cosetBranchBlock_0135 b
  · exact g32p_row13_cosetBranchBlock_0136 b
  · exact g32p_row13_cosetBranchBlock_0137 b
  · exact g32p_row13_cosetBranchBlock_0138 b
  · exact g32p_row13_cosetBranchBlock_0139 b
  · exact g32p_row13_cosetBranchBlock_0140 b
  · exact g32p_row13_cosetBranchBlock_0141 b
  · exact g32p_row13_cosetBranchBlock_0142 b
  · exact g32p_row13_cosetBranchBlock_0143 b
  · exact g32p_row13_cosetBranchBlock_0144 b
  · exact g32p_row13_cosetBranchBlock_0145 b
  · exact g32p_row13_cosetBranchBlock_0146 b
  · exact g32p_row13_cosetBranchBlock_0147 b
  · exact g32p_row13_cosetBranchBlock_0148 b
  · exact g32p_row13_cosetBranchBlock_0149 b
  · exact g32p_row13_cosetBranchBlock_0150 b
  · exact g32p_row13_cosetBranchBlock_0151 b
  · exact g32p_row13_cosetBranchBlock_0152 b
  · exact g32p_row13_cosetBranchBlock_0153 b
  · exact g32p_row13_cosetBranchBlock_0154 b
  · exact g32p_row13_cosetBranchBlock_0155 b
  · exact g32p_row13_cosetBranchBlock_0156 b
  · exact g32p_row13_cosetBranchBlock_0157 b
  · exact g32p_row13_cosetBranchBlock_0158 b
  · exact g32p_row13_cosetBranchBlock_0159 b
  · exact g32p_row13_cosetBranchBlock_0160 b
  · exact g32p_row13_cosetBranchBlock_0161 b
  · exact g32p_row13_cosetBranchBlock_0162 b
  · exact g32p_row13_cosetBranchBlock_0163 b
  · exact g32p_row13_cosetBranchBlock_0164 b
  · exact g32p_row13_cosetBranchBlock_0165 b
  · exact g32p_row13_cosetBranchBlock_0166 b
  · exact g32p_row13_cosetBranchBlock_0167 b
  · exact g32p_row13_cosetBranchBlock_0168 b
  · exact g32p_row13_cosetBranchBlock_0169 b
  · exact g32p_row13_cosetBranchBlock_0170 b
  · exact g32p_row13_cosetBranchBlock_0171 b
  · exact g32p_row13_cosetBranchBlock_0172 b
  · exact g32p_row13_cosetBranchBlock_0173 b
  · exact g32p_row13_cosetBranchBlock_0174 b
  · exact g32p_row13_cosetBranchBlock_0175 b
  · exact g32p_row13_cosetBranchBlock_0176 b
  · exact g32p_row13_cosetBranchBlock_0177 b
  · exact g32p_row13_cosetBranchBlock_0178 b
  · exact g32p_row13_cosetBranchBlock_0179 b
  · exact g32p_row13_cosetBranchBlock_0180 b
  · exact g32p_row13_cosetBranchBlock_0181 b
  · exact g32p_row13_cosetBranchBlock_0182 b
  · exact g32p_row13_cosetBranchBlock_0183 b
  · exact g32p_row13_cosetBranchBlock_0184 b
  · exact g32p_row13_cosetBranchBlock_0185 b
  · exact g32p_row13_cosetBranchBlock_0186 b
  · exact g32p_row13_cosetBranchBlock_0187 b
  · exact g32p_row13_cosetBranchBlock_0188 b
  · exact g32p_row13_cosetBranchBlock_0189 b
  · exact g32p_row13_cosetBranchBlock_0190 b
  · exact g32p_row13_cosetBranchBlock_0191 b
  · exact g32p_row13_cosetBranchBlock_0192 b
  · exact g32p_row13_cosetBranchBlock_0193 b
  · exact g32p_row13_cosetBranchBlock_0194 b
  · exact g32p_row13_cosetBranchBlock_0195 b
  · exact g32p_row13_cosetBranchBlock_0196 b
  · exact g32p_row13_cosetBranchBlock_0197 b
  · exact g32p_row13_cosetBranchBlock_0198 b
  · exact g32p_row13_cosetBranchBlock_0199 b
  · exact g32p_row13_cosetBranchBlock_0200 b
  · exact g32p_row13_cosetBranchBlock_0201 b
  · exact g32p_row13_cosetBranchBlock_0202 b
  · exact g32p_row13_cosetBranchBlock_0203 b
  · exact g32p_row13_cosetBranchBlock_0204 b
  · exact g32p_row13_cosetBranchBlock_0205 b
  · exact g32p_row13_cosetBranchBlock_0206 b
  · exact g32p_row13_cosetBranchBlock_0207 b
  · exact g32p_row13_cosetBranchBlock_0208 b
  · exact g32p_row13_cosetBranchBlock_0209 b
  · exact g32p_row13_cosetBranchBlock_0210 b
  · exact g32p_row13_cosetBranchBlock_0211 b
  · exact g32p_row13_cosetBranchBlock_0212 b
  · exact g32p_row13_cosetBranchBlock_0213 b
  · exact g32p_row13_cosetBranchBlock_0214 b
  · exact g32p_row13_cosetBranchBlock_0215 b
  · exact g32p_row13_cosetBranchBlock_0216 b
  · exact g32p_row13_cosetBranchBlock_0217 b
  · exact g32p_row13_cosetBranchBlock_0218 b
  · exact g32p_row13_cosetBranchBlock_0219 b
  · exact g32p_row13_cosetBranchBlock_0220 b
  · exact g32p_row13_cosetBranchBlock_0221 b
  · exact g32p_row13_cosetBranchBlock_0222 b
  · exact g32p_row13_cosetBranchBlock_0223 b
  · exact g32p_row13_cosetBranchBlock_0224 b
  · exact g32p_row13_cosetBranchBlock_0225 b
  · exact g32p_row13_cosetBranchBlock_0226 b
  · exact g32p_row13_cosetBranchBlock_0227 b
  · exact g32p_row13_cosetBranchBlock_0228 b
  · exact g32p_row13_cosetBranchBlock_0229 b
  · exact g32p_row13_cosetBranchBlock_0230 b
  · exact g32p_row13_cosetBranchBlock_0231 b
  · exact g32p_row13_cosetBranchBlock_0232 b
  · exact g32p_row13_cosetBranchBlock_0233 b
  · exact g32p_row13_cosetBranchBlock_0234 b
  · exact g32p_row13_cosetBranchBlock_0235 b
  · exact g32p_row13_cosetBranchBlock_0236 b
  · exact g32p_row13_cosetBranchBlock_0237 b
  · exact g32p_row13_cosetBranchBlock_0238 b
  · exact g32p_row13_cosetBranchBlock_0239 b
  · exact g32p_row13_cosetBranchBlock_0240 b
  · exact g32p_row13_cosetBranchBlock_0241 b
  · exact g32p_row13_cosetBranchBlock_0242 b
  · exact g32p_row13_cosetBranchBlock_0243 b
  · exact g32p_row13_cosetBranchBlock_0244 b
  · exact g32p_row13_cosetBranchBlock_0245 b
  · exact g32p_row13_cosetBranchBlock_0246 b
  · exact g32p_row13_cosetBranchBlock_0247 b
  · exact g32p_row13_cosetBranchBlock_0248 b
  · exact g32p_row13_cosetBranchBlock_0249 b
  · exact g32p_row13_cosetBranchBlock_0250 b
  · exact g32p_row13_cosetBranchBlock_0251 b
  · exact g32p_row13_cosetBranchBlock_0252 b
  · exact g32p_row13_cosetBranchBlock_0253 b
  · exact g32p_row13_cosetBranchBlock_0254 b
  · exact g32p_row13_cosetBranchBlock_0255 b
  · exact g32p_row13_cosetBranchBlock_0256 b
  · exact g32p_row13_cosetBranchBlock_0257 b
  · exact g32p_row13_cosetBranchBlock_0258 b
  · exact g32p_row13_cosetBranchBlock_0259 b
  · exact g32p_row13_cosetBranchBlock_0260 b
  · exact g32p_row13_cosetBranchBlock_0261 b
  · exact g32p_row13_cosetBranchBlock_0262 b
  · exact g32p_row13_cosetBranchBlock_0263 b
  · exact g32p_row13_cosetBranchBlock_0264 b
  · exact g32p_row13_cosetBranchBlock_0265 b
  · exact g32p_row13_cosetBranchBlock_0266 b
  · exact g32p_row13_cosetBranchBlock_0267 b
  · exact g32p_row13_cosetBranchBlock_0268 b
  · exact g32p_row13_cosetBranchBlock_0269 b
  · exact g32p_row13_cosetBranchBlock_0270 b
  · exact g32p_row13_cosetBranchBlock_0271 b
  · exact g32p_row13_cosetBranchBlock_0272 b
  · exact g32p_row13_cosetBranchBlock_0273 b
  · exact g32p_row13_cosetBranchBlock_0274 b
  · exact g32p_row13_cosetBranchBlock_0275 b
  · exact g32p_row13_cosetBranchBlock_0276 b
  · exact g32p_row13_cosetBranchBlock_0277 b
  · exact g32p_row13_cosetBranchBlock_0278 b
  · exact g32p_row13_cosetBranchBlock_0279 b
  · exact g32p_row13_cosetBranchBlock_0280 b
  · exact g32p_row13_cosetBranchBlock_0281 b
  · exact g32p_row13_cosetBranchBlock_0282 b
  · exact g32p_row13_cosetBranchBlock_0283 b
  · exact g32p_row13_cosetBranchBlock_0284 b
  · exact g32p_row13_cosetBranchBlock_0285 b
  · exact g32p_row13_cosetBranchBlock_0286 b
  · exact g32p_row13_cosetBranchBlock_0287 b
  · exact g32p_row13_cosetBranchBlock_0288 b
  · exact g32p_row13_cosetBranchBlock_0289 b
  · exact g32p_row13_cosetBranchBlock_0290 b
  · exact g32p_row13_cosetBranchBlock_0291 b
  · exact g32p_row13_cosetBranchBlock_0292 b
  · exact g32p_row13_cosetBranchBlock_0293 b
  · exact g32p_row13_cosetBranchBlock_0294 b
  · exact g32p_row13_cosetBranchBlock_0295 b
  · exact g32p_row13_cosetBranchBlock_0296 b
  · exact g32p_row13_cosetBranchBlock_0297 b
  · exact g32p_row13_cosetBranchBlock_0298 b
  · exact g32p_row13_cosetBranchBlock_0299 b
  · exact g32p_row13_cosetBranchBlock_0300 b
  · exact g32p_row13_cosetBranchBlock_0301 b
  · exact g32p_row13_cosetBranchBlock_0302 b
  · exact g32p_row13_cosetBranchBlock_0303 b
  · exact g32p_row13_cosetBranchBlock_0304 b
  · exact g32p_row13_cosetBranchBlock_0305 b
  · exact g32p_row13_cosetBranchBlock_0306 b
  · exact g32p_row13_cosetBranchBlock_0307 b
  · exact g32p_row13_cosetBranchBlock_0308 b
  · exact g32p_row13_cosetBranchBlock_0309 b
  · exact g32p_row13_cosetBranchBlock_0310 b
  · exact g32p_row13_cosetBranchBlock_0311 b
  · exact g32p_row13_cosetBranchBlock_0312 b
  · exact g32p_row13_cosetBranchBlock_0313 b
  · exact g32p_row13_cosetBranchBlock_0314 b
  · exact g32p_row13_cosetBranchBlock_0315 b
  · exact g32p_row13_cosetBranchBlock_0316 b
  · exact g32p_row13_cosetBranchBlock_0317 b
  · exact g32p_row13_cosetBranchBlock_0318 b
  · exact g32p_row13_cosetBranchBlock_0319 b
  · exact g32p_row13_cosetBranchBlock_0320 b
  · exact g32p_row13_cosetBranchBlock_0321 b
  · exact g32p_row13_cosetBranchBlock_0322 b
  · exact g32p_row13_cosetBranchBlock_0323 b
  · exact g32p_row13_cosetBranchBlock_0324 b
  · exact g32p_row13_cosetBranchBlock_0325 b
  · exact g32p_row13_cosetBranchBlock_0326 b
  · exact g32p_row13_cosetBranchBlock_0327 b
  · exact g32p_row13_cosetBranchBlock_0328 b
  · exact g32p_row13_cosetBranchBlock_0329 b
  · exact g32p_row13_cosetBranchBlock_0330 b
  · exact g32p_row13_cosetBranchBlock_0331 b
  · exact g32p_row13_cosetBranchBlock_0332 b
  · exact g32p_row13_cosetBranchBlock_0333 b
  · exact g32p_row13_cosetBranchBlock_0334 b
  · exact g32p_row13_cosetBranchBlock_0335 b
  · exact g32p_row13_cosetBranchBlock_0336 b
  · exact g32p_row13_cosetBranchBlock_0337 b
  · exact g32p_row13_cosetBranchBlock_0338 b
  · exact g32p_row13_cosetBranchBlock_0339 b
  · exact g32p_row13_cosetBranchBlock_0340 b
  · exact g32p_row13_cosetBranchBlock_0341 b
  · exact g32p_row13_cosetBranchBlock_0342 b
  · exact g32p_row13_cosetBranchBlock_0343 b
  · exact g32p_row13_cosetBranchBlock_0344 b
  · exact g32p_row13_cosetBranchBlock_0345 b
  · exact g32p_row13_cosetBranchBlock_0346 b
  · exact g32p_row13_cosetBranchBlock_0347 b
  · exact g32p_row13_cosetBranchBlock_0348 b
  · exact g32p_row13_cosetBranchBlock_0349 b
  · exact g32p_row13_cosetBranchBlock_0350 b
  · exact g32p_row13_cosetBranchBlock_0351 b
  · exact g32p_row13_cosetBranchBlock_0352 b
  · exact g32p_row13_cosetBranchBlock_0353 b
  · exact g32p_row13_cosetBranchBlock_0354 b
  · exact g32p_row13_cosetBranchBlock_0355 b
  · exact g32p_row13_cosetBranchBlock_0356 b
  · exact g32p_row13_cosetBranchBlock_0357 b
  · exact g32p_row13_cosetBranchBlock_0358 b
  · exact g32p_row13_cosetBranchBlock_0359 b
  · exact g32p_row13_cosetBranchBlock_0360 b
  · exact g32p_row13_cosetBranchBlock_0361 b
  · exact g32p_row13_cosetBranchBlock_0362 b
  · exact g32p_row13_cosetBranchBlock_0363 b
  · exact g32p_row13_cosetBranchBlock_0364 b
  · exact g32p_row13_cosetBranchBlock_0365 b
  · exact g32p_row13_cosetBranchBlock_0366 b
  · exact g32p_row13_cosetBranchBlock_0367 b
  · exact g32p_row13_cosetBranchBlock_0368 b
  · exact g32p_row13_cosetBranchBlock_0369 b
  · exact g32p_row13_cosetBranchBlock_0370 b
  · exact g32p_row13_cosetBranchBlock_0371 b
  · exact g32p_row13_cosetBranchBlock_0372 b
  · exact g32p_row13_cosetBranchBlock_0373 b
  · exact g32p_row13_cosetBranchBlock_0374 b
  · exact g32p_row13_cosetBranchBlock_0375 b
  · exact g32p_row13_cosetBranchBlock_0376 b
  · exact g32p_row13_cosetBranchBlock_0377 b
  · exact g32p_row13_cosetBranchBlock_0378 b
  · exact g32p_row13_cosetBranchBlock_0379 b
  · exact g32p_row13_cosetBranchBlock_0380 b
  · exact g32p_row13_cosetBranchBlock_0381 b
  · exact g32p_row13_cosetBranchBlock_0382 b
  · exact g32p_row13_cosetBranchBlock_0383 b
  · exact g32p_row13_cosetBranchBlock_0384 b
  · exact g32p_row13_cosetBranchBlock_0385 b
  · exact g32p_row13_cosetBranchBlock_0386 b
  · exact g32p_row13_cosetBranchBlock_0387 b
  · exact g32p_row13_cosetBranchBlock_0388 b
  · exact g32p_row13_cosetBranchBlock_0389 b
  · exact g32p_row13_cosetBranchBlock_0390 b
  · exact g32p_row13_cosetBranchBlock_0391 b
  · exact g32p_row13_cosetBranchBlock_0392 b
  · exact g32p_row13_cosetBranchBlock_0393 b
  · exact g32p_row13_cosetBranchBlock_0394 b
  · exact g32p_row13_cosetBranchBlock_0395 b
  · exact g32p_row13_cosetBranchBlock_0396 b
  · exact g32p_row13_cosetBranchBlock_0397 b
  · exact g32p_row13_cosetBranchBlock_0398 b
  · exact g32p_row13_cosetBranchBlock_0399 b
  · exact g32p_row13_cosetBranchBlock_0400 b
  · exact g32p_row13_cosetBranchBlock_0401 b
  · exact g32p_row13_cosetBranchBlock_0402 b
  · exact g32p_row13_cosetBranchBlock_0403 b
  · exact g32p_row13_cosetBranchBlock_0404 b


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_cosetBranchMap (b : Fin 3) :
    b4b_toMatrix (g32p_cosetBranches b) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row13_cosetBranchMatrices b)) := by
  have he : g32p_row13_cosetBranchMatrices b = g32p_cosetIntegralBranches b := by
    revert b
    decide +kernel
  rw [he]
  exact g32p_cosetBranches_map b

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_cosetActualBranchStep (b : Fin 3) (i : Fin 6480) :
    g32p_cosetBranches b * g32p_row13_cosetActualRepresentatives i =
      g32p_row13_cosetActualRepresentatives (g32p_row13_cosetBranchNext b i) *
        (g32p_row13_groupEquiv (g32p_row13_cosetBranchFactor b i) : g32p_G) := by
  apply Subtype.ext
  change b4b_toMatrix (g32p_cosetBranches b * g32p_row13_cosetActualRepresentatives i) =
    b4b_toMatrix (g32p_row13_cosetActualRepresentatives (g32p_row13_cosetBranchNext b i) *
      (g32p_row13_groupEquiv (g32p_row13_cosetBranchFactor b i) : g32p_G))
  rw [map_mul, map_mul, g32p_row13_cosetBranchMap, g32p_row13_cosetActualRepresentatives_map,
    g32p_row13_cosetActualRepresentatives_map, g32p_row13_groupEquiv_map,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add, g32p_row13_cosetBranchCheck]

end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

def g32p_finWideBlockIndex (n : ℕ) [NeZero n] (q : ℕ) (r : Fin 512) : Fin n :=
  Fin.ofNat n (q * 512 + r.val)

theorem g32p_forall_fin_wide_blocks {n : ℕ} [NeZero n] (P : Fin n → Prop)
    (h : ∀ q : Fin ((n + 511) / 512), ∀ r : Fin 512,
      P (g32p_finWideBlockIndex n q.val r)) : ∀ i, P i := by
  intro i
  have hq : i.val / 512 < (n + 511) / 512 := by omega
  have he : g32p_finWideBlockIndex n (i.val / 512)
      ⟨i.val % 512, Nat.mod_lt _ (by decide)⟩ = i := by
    apply Fin.ext
    change (i.val / 512 * 512 + i.val % 512) % n = i.val
    rw [Nat.mul_comm (i.val / 512) 512, Nat.div_add_mod, Nat.mod_eq_of_lt i.isLt]
  exact he ▸ h ⟨i.val / 512, hq⟩ ⟨i.val % 512, Nat.mod_lt _ (by decide)⟩

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_involutionPart0000 (r : Fin 512) :
    let j := g32p_finWideBlockIndex 3312 0 r
    ((g32p_row13_cosetLengths2 j = 1 ∧
      g32p_row13_cosetBranchNext 2 (g32p_row13_cosetRoots2 j) = g32p_row13_cosetRoots2 j ∧
      g32p_row13_cosetMonodromies2 j = g32p_row13_cosetBranchFactor 2 (g32p_row13_cosetRoots2 j)) ∨
    (g32p_row13_cosetLengths2 j = 2 ∧ g32p_row13_cosetMonodromies2 j = 0)) ∧
    g32p_row13_characterValues (g32p_row13_cosetMonodromies2 j) = g32p_row13_cosetExponents2 j := by
  revert r
  decide +kernel

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_involutionPart0001 (r : Fin 512) :
    let j := g32p_finWideBlockIndex 3312 1 r
    ((g32p_row13_cosetLengths2 j = 1 ∧
      g32p_row13_cosetBranchNext 2 (g32p_row13_cosetRoots2 j) = g32p_row13_cosetRoots2 j ∧
      g32p_row13_cosetMonodromies2 j = g32p_row13_cosetBranchFactor 2 (g32p_row13_cosetRoots2 j)) ∨
    (g32p_row13_cosetLengths2 j = 2 ∧ g32p_row13_cosetMonodromies2 j = 0)) ∧
    g32p_row13_characterValues (g32p_row13_cosetMonodromies2 j) = g32p_row13_cosetExponents2 j := by
  revert r
  decide +kernel

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_involutionPart0002 (r : Fin 512) :
    let j := g32p_finWideBlockIndex 3312 2 r
    ((g32p_row13_cosetLengths2 j = 1 ∧
      g32p_row13_cosetBranchNext 2 (g32p_row13_cosetRoots2 j) = g32p_row13_cosetRoots2 j ∧
      g32p_row13_cosetMonodromies2 j = g32p_row13_cosetBranchFactor 2 (g32p_row13_cosetRoots2 j)) ∨
    (g32p_row13_cosetLengths2 j = 2 ∧ g32p_row13_cosetMonodromies2 j = 0)) ∧
    g32p_row13_characterValues (g32p_row13_cosetMonodromies2 j) = g32p_row13_cosetExponents2 j := by
  revert r
  decide +kernel

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_involutionPart0003 (r : Fin 512) :
    let j := g32p_finWideBlockIndex 3312 3 r
    ((g32p_row13_cosetLengths2 j = 1 ∧
      g32p_row13_cosetBranchNext 2 (g32p_row13_cosetRoots2 j) = g32p_row13_cosetRoots2 j ∧
      g32p_row13_cosetMonodromies2 j = g32p_row13_cosetBranchFactor 2 (g32p_row13_cosetRoots2 j)) ∨
    (g32p_row13_cosetLengths2 j = 2 ∧ g32p_row13_cosetMonodromies2 j = 0)) ∧
    g32p_row13_characterValues (g32p_row13_cosetMonodromies2 j) = g32p_row13_cosetExponents2 j := by
  revert r
  decide +kernel

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_involutionPart0004 (r : Fin 512) :
    let j := g32p_finWideBlockIndex 3312 4 r
    ((g32p_row13_cosetLengths2 j = 1 ∧
      g32p_row13_cosetBranchNext 2 (g32p_row13_cosetRoots2 j) = g32p_row13_cosetRoots2 j ∧
      g32p_row13_cosetMonodromies2 j = g32p_row13_cosetBranchFactor 2 (g32p_row13_cosetRoots2 j)) ∨
    (g32p_row13_cosetLengths2 j = 2 ∧ g32p_row13_cosetMonodromies2 j = 0)) ∧
    g32p_row13_characterValues (g32p_row13_cosetMonodromies2 j) = g32p_row13_cosetExponents2 j := by
  revert r
  decide +kernel

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_involutionPart0005 (r : Fin 512) :
    let j := g32p_finWideBlockIndex 3312 5 r
    ((g32p_row13_cosetLengths2 j = 1 ∧
      g32p_row13_cosetBranchNext 2 (g32p_row13_cosetRoots2 j) = g32p_row13_cosetRoots2 j ∧
      g32p_row13_cosetMonodromies2 j = g32p_row13_cosetBranchFactor 2 (g32p_row13_cosetRoots2 j)) ∨
    (g32p_row13_cosetLengths2 j = 2 ∧ g32p_row13_cosetMonodromies2 j = 0)) ∧
    g32p_row13_characterValues (g32p_row13_cosetMonodromies2 j) = g32p_row13_cosetExponents2 j := by
  revert r
  decide +kernel

end HodgeLean.Foundations.Program

end
