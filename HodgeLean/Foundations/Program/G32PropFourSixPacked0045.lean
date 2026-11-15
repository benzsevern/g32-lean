import HodgeLean.Foundations.Program.G32PropFourSixPacked0043
import HodgeLean.Foundations.Program.G32PropFourSixPacked0044
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixFiniteCheck
import HodgeLean.Foundations.Program.G32PropFourSixArchiveReverse

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row04_groupWords : Fin 3 → List (Fin 4) :=
  ![[0, 1, 0, 0, 3, 2, 2, 0, 0, 3, 1, 1, 0, 0, 1, 2, 2], [2, 0, 0, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2], [2, 2, 3, 0, 0, 3, 2, 2, 1, 0, 0, 1, 2, 2]]

def g32p_row04_groupMatrices : Fin 3 → HurwitzPrymRex_Mat :=
  ![![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]], ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]], ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]]

def g32p_row04_groupGenerators : Fin 3 → g32p_G :=
  fun s => g32p_archiveWord (g32p_row04_groupWords s)

def g32p_row04_groupStages_0 : List HurwitzPrymRex_Mat :=
  [![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
   ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]],
   ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row04_groupCertificate_0 :
    g32p_archiveWordCertificate (g32p_row04_groupWords 0)
      g32p_row04_groupStages_0 = true := by
  decide +kernel

theorem g32p_row04_groupIntegral_0 :
    g32p_archiveIntegralWord (g32p_row04_groupWords 0) =
      g32p_row04_groupMatrices 0 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row04_groupCertificate_0
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row04_groupMatrices 0 := by
    exact ht.symm.trans (show g32p_row04_groupStages_0.headD HurwitzPrymRex_mone =
      g32p_row04_groupMatrices 0 by decide)
  exact hv.trans ha

def g32p_row04_groupStages_1 : List HurwitzPrymRex_Mat :=
  [![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]],
   ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]],
   ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row04_groupCertificate_1 :
    g32p_archiveWordCertificate (g32p_row04_groupWords 1)
      g32p_row04_groupStages_1 = true := by
  decide +kernel

theorem g32p_row04_groupIntegral_1 :
    g32p_archiveIntegralWord (g32p_row04_groupWords 1) =
      g32p_row04_groupMatrices 1 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row04_groupCertificate_1
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row04_groupMatrices 1 := by
    exact ht.symm.trans (show g32p_row04_groupStages_1.headD HurwitzPrymRex_mone =
      g32p_row04_groupMatrices 1 by decide)
  exact hv.trans ha

def g32p_row04_groupStages_2 : List HurwitzPrymRex_Mat :=
  [![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]],
   ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row04_groupCertificate_2 :
    g32p_archiveWordCertificate (g32p_row04_groupWords 2)
      g32p_row04_groupStages_2 = true := by
  decide +kernel

theorem g32p_row04_groupIntegral_2 :
    g32p_archiveIntegralWord (g32p_row04_groupWords 2) =
      g32p_row04_groupMatrices 2 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row04_groupCertificate_2
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row04_groupMatrices 2 := by
    exact ht.symm.trans (show g32p_row04_groupStages_2.headD HurwitzPrymRex_mone =
      g32p_row04_groupMatrices 2 by decide)
  exact hv.trans ha

theorem g32p_row04_groupGenerator_map (s : Fin 3) :
    b4b_toMatrix (g32p_row04_groupGenerators s) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
        (g32p_row04_groupMatrices s)) := by
  rw [g32p_row04_groupGenerators, g32p_archiveIntegralWord_map]
  apply congrArg (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
  fin_cases s
  · exact g32p_row04_groupIntegral_0
  · exact g32p_row04_groupIntegral_1
  · exact g32p_row04_groupIntegral_2

def g32p_row04_groupNodes : Fin 1728 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 896 then
(if i.val < 384 then
(if i.val < 128 then
g32p_row04_Nodes00 i
else
(if i.val < 256 then
g32p_row04_Nodes01 i
else
g32p_row04_Nodes02 i))
else
(if i.val < 640 then
(if i.val < 512 then
g32p_row04_Nodes03 i
else
g32p_row04_Nodes04 i)
else
(if i.val < 768 then
g32p_row04_Nodes05 i
else
g32p_row04_Nodes06 i)))
else
(if i.val < 1280 then
(if i.val < 1024 then
g32p_row04_Nodes07 i
else
(if i.val < 1152 then
g32p_row04_Nodes08 i
else
g32p_row04_Nodes09 i))
else
(if i.val < 1536 then
(if i.val < 1408 then
g32p_row04_Nodes10 i
else
g32p_row04_Nodes11 i)
else
(if i.val < 1664 then
g32p_row04_Nodes12 i
else
g32p_row04_Nodes13 i))))


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row04_characterBlock_000 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 0 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 0 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_001 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 1 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 1 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_002 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 2 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 2 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_003 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 3 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 3 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_004 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 4 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 4 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_005 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 5 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 5 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_006 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 6 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 6 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_007 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 7 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 7 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_008 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 8 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 8 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_009 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 9 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 9 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_010 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 10 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 10 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_011 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 11 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 11 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_012 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 12 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 12 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_013 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 13 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 13 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_014 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 14 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 14 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_015 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 15 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 15 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_016 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 16 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 16 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_017 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 17 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 17 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_018 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 18 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 18 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_019 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 19 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 19 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_020 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 20 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 20 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_021 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 21 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 21 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_022 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 22 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 22 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_023 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 23 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 23 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_024 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 24 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 24 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_025 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 25 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 25 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_026 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 26 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 26 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_027 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 27 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 27 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_028 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 28 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 28 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_029 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 29 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 29 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_030 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 30 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 30 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_031 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 31 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 31 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_032 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 32 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 32 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_033 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 33 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 33 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_034 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 34 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 34 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_035 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 35 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 35 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_036 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 36 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 36 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_037 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 37 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 37 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_038 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 38 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 38 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_039 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 39 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 39 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_040 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 40 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 40 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_041 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 41 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 41 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_042 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 42 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 42 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_043 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 43 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 43 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_044 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 44 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 44 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_045 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 45 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 45 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_046 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 46 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 46 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_047 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 47 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 47 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_048 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 48 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 48 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_049 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 49 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 49 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_050 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 50 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 50 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_051 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 51 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 51 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_052 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 52 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 52 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_053 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 53 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 53 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_054 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 54 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 54 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_055 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 55 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 55 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_056 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 56 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 56 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_057 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 57 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 57 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_058 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 58 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 58 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_059 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 59 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 59 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_060 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 60 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 60 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_061 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 61 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 61 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_062 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 62 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 62 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_063 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 63 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 63 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row04_characterBlock_064 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 64 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 64 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_065 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 65 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 65 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_066 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 66 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 66 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_067 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 67 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 67 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_068 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 68 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 68 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_069 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 69 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 69 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_070 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 70 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 70 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_071 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 71 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 71 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_072 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 72 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 72 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_073 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 73 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 73 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_074 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 74 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 74 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_075 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 75 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 75 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_076 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 76 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 76 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_077 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 77 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 77 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_078 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 78 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 78 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_079 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 79 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 79 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_080 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 80 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 80 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_081 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 81 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 81 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_082 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 82 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 82 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_083 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 83 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 83 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_084 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 84 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 84 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_085 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 85 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 85 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_086 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 86 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 86 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_087 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 87 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 87 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_088 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 88 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 88 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_089 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 89 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 89 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_090 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 90 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 90 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_091 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 91 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 91 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_092 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 92 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 92 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_093 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 93 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 93 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_094 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 94 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 94 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_095 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 95 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 95 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_096 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 96 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 96 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_097 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 97 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 97 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_098 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 98 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 98 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_099 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 99 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 99 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_100 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 100 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 100 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_101 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 101 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 101 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_102 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 102 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 102 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_103 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 103 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 103 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_104 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 104 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 104 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_105 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 105 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 105 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_106 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 106 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 106 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel

theorem g32p_row04_characterBlock_107 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row04_characterValues (g32p_row04_groupNext (g32p_finBlockIndex 1728 107 r) s) = g32p_row04_characterValues (g32p_finBlockIndex 1728 107 r) * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end
