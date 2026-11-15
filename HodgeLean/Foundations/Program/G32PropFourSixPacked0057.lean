import HodgeLean.Foundations.Program.G32PropFourSixPacked0055
import HodgeLean.Foundations.Program.G32PropFourSixPacked0056
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixFiniteCheck
import HodgeLean.Foundations.Program.G32PropFourSixArchiveReverse

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row07_groupWords : Fin 4 → List (Fin 4) :=
  ![[1, 3, 3, 2, 0, 3, 3, 1, 1, 2, 0, 1, 1, 3], [0, 3, 3, 0, 0], [1, 2, 3, 3, 2, 0, 3, 3, 1, 1, 2, 0, 1, 3, 2, 2, 0, 0, 3, 3], [1, 1, 2, 1, 0, 0, 1, 1, 3, 2, 1, 0, 0, 3]]

def g32p_row07_groupMatrices : Fin 4 → HurwitzPrymRex_Mat :=
  ![![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]], ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]], ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]], ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]]

def g32p_row07_groupGenerators : Fin 4 → g32p_G :=
  fun s => g32p_archiveWord (g32p_row07_groupWords s)

def g32p_row07_groupStages_0 : List HurwitzPrymRex_Mat :=
  [![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]],
   ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]],
   ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
   ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
   ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
   ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]],
   ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]],
   ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]],
   ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]],
   ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row07_groupCertificate_0 :
    g32p_archiveWordCertificate (g32p_row07_groupWords 0)
      g32p_row07_groupStages_0 = true := by
  decide +kernel

theorem g32p_row07_groupIntegral_0 :
    g32p_archiveIntegralWord (g32p_row07_groupWords 0) =
      g32p_row07_groupMatrices 0 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row07_groupCertificate_0
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row07_groupMatrices 0 := by
    exact ht.symm.trans (show g32p_row07_groupStages_0.headD HurwitzPrymRex_mone =
      g32p_row07_groupMatrices 0 by decide)
  exact hv.trans ha

def g32p_row07_groupStages_1 : List HurwitzPrymRex_Mat :=
  [![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row07_groupCertificate_1 :
    g32p_archiveWordCertificate (g32p_row07_groupWords 1)
      g32p_row07_groupStages_1 = true := by
  decide +kernel

theorem g32p_row07_groupIntegral_1 :
    g32p_archiveIntegralWord (g32p_row07_groupWords 1) =
      g32p_row07_groupMatrices 1 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row07_groupCertificate_1
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row07_groupMatrices 1 := by
    exact ht.symm.trans (show g32p_row07_groupStages_1.headD HurwitzPrymRex_mone =
      g32p_row07_groupMatrices 1 by decide)
  exact hv.trans ha

def g32p_row07_groupStages_2 : List HurwitzPrymRex_Mat :=
  [![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]],
   ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]],
   ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]],
   ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]],
   ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]],
   ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]],
   ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]],
   ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
   ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row07_groupCertificate_2 :
    g32p_archiveWordCertificate (g32p_row07_groupWords 2)
      g32p_row07_groupStages_2 = true := by
  decide +kernel

theorem g32p_row07_groupIntegral_2 :
    g32p_archiveIntegralWord (g32p_row07_groupWords 2) =
      g32p_row07_groupMatrices 2 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row07_groupCertificate_2
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row07_groupMatrices 2 := by
    exact ht.symm.trans (show g32p_row07_groupStages_2.headD HurwitzPrymRex_mone =
      g32p_row07_groupMatrices 2 by decide)
  exact hv.trans ha

def g32p_row07_groupStages_3 : List HurwitzPrymRex_Mat :=
  [![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]],
   ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]],
   ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]],
   ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 2⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row07_groupCertificate_3 :
    g32p_archiveWordCertificate (g32p_row07_groupWords 3)
      g32p_row07_groupStages_3 = true := by
  decide +kernel

theorem g32p_row07_groupIntegral_3 :
    g32p_archiveIntegralWord (g32p_row07_groupWords 3) =
      g32p_row07_groupMatrices 3 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row07_groupCertificate_3
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row07_groupMatrices 3 := by
    exact ht.symm.trans (show g32p_row07_groupStages_3.headD HurwitzPrymRex_mone =
      g32p_row07_groupMatrices 3 by decide)
  exact hv.trans ha

theorem g32p_row07_groupGenerator_map (s : Fin 4) :
    b4b_toMatrix (g32p_row07_groupGenerators s) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
        (g32p_row07_groupMatrices s)) := by
  rw [g32p_row07_groupGenerators, g32p_archiveIntegralWord_map]
  apply congrArg (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
  fin_cases s
  · exact g32p_row07_groupIntegral_0
  · exact g32p_row07_groupIntegral_1
  · exact g32p_row07_groupIntegral_2
  · exact g32p_row07_groupIntegral_3

def g32p_row07_groupNodes : Fin 1944 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 1024 then
(if i.val < 512 then
(if i.val < 256 then
(if i.val < 128 then
g32p_row07_Nodes00 i
else
g32p_row07_Nodes01 i)
else
(if i.val < 384 then
g32p_row07_Nodes02 i
else
g32p_row07_Nodes03 i))
else
(if i.val < 768 then
(if i.val < 640 then
g32p_row07_Nodes04 i
else
g32p_row07_Nodes05 i)
else
(if i.val < 896 then
g32p_row07_Nodes06 i
else
g32p_row07_Nodes07 i)))
else
(if i.val < 1536 then
(if i.val < 1280 then
(if i.val < 1152 then
g32p_row07_Nodes08 i
else
g32p_row07_Nodes09 i)
else
(if i.val < 1408 then
g32p_row07_Nodes10 i
else
g32p_row07_Nodes11 i))
else
(if i.val < 1792 then
(if i.val < 1664 then
g32p_row07_Nodes12 i
else
g32p_row07_Nodes13 i)
else
(if i.val < 1920 then
g32p_row07_Nodes14 i
else
g32p_row07_Nodes15 i))))


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row07_characterBlock_000 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 0 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 0 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_001 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 1 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 1 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_002 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 2 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 2 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_003 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 3 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 3 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_004 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 4 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 4 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_005 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 5 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 5 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_006 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 6 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 6 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_007 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 7 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 7 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_008 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 8 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 8 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_009 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 9 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 9 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_010 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 10 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 10 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_011 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 11 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 11 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_012 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 12 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 12 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_013 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 13 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 13 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_014 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 14 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 14 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_015 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 15 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 15 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_016 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 16 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 16 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_017 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 17 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 17 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_018 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 18 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 18 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_019 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 19 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 19 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_020 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 20 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 20 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_021 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 21 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 21 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_022 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 22 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 22 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_023 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 23 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 23 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_024 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 24 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 24 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_025 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 25 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 25 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_026 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 26 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 26 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_027 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 27 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 27 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_028 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 28 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 28 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_029 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 29 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 29 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_030 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 30 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 30 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_031 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 31 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 31 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_032 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 32 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 32 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_033 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 33 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 33 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_034 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 34 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 34 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_035 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 35 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 35 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_036 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 36 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 36 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_037 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 37 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 37 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_038 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 38 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 38 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_039 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 39 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 39 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_040 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 40 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 40 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_041 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 41 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 41 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_042 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 42 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 42 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_043 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 43 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 43 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_044 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 44 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 44 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_045 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 45 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 45 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_046 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 46 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 46 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_047 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 47 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 47 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_048 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 48 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 48 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_049 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 49 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 49 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_050 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 50 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 50 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_051 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 51 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 51 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_052 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 52 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 52 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_053 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 53 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 53 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_054 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 54 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 54 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_055 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 55 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 55 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_056 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 56 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 56 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_057 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 57 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 57 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_058 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 58 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 58 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_059 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 59 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 59 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_060 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 60 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 60 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_061 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 61 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 61 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_062 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 62 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 62 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_063 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 63 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 63 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
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

theorem g32p_row07_characterBlock_064 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 64 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 64 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_065 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 65 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 65 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_066 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 66 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 66 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_067 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 67 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 67 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_068 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 68 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 68 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_069 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 69 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 69 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_070 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 70 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 70 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_071 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 71 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 71 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_072 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 72 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 72 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_073 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 73 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 73 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_074 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 74 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 74 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_075 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 75 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 75 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_076 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 76 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 76 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_077 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 77 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 77 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_078 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 78 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 78 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_079 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 79 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 79 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_080 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 80 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 80 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_081 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 81 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 81 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_082 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 82 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 82 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_083 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 83 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 83 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_084 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 84 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 84 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_085 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 85 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 85 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_086 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 86 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 86 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_087 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 87 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 87 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_088 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 88 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 88 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_089 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 89 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 89 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_090 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 90 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 90 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_091 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 91 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 91 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_092 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 92 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 92 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_093 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 93 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 93 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_094 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 94 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 94 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_095 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 95 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 95 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_096 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 96 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 96 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_097 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 97 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 97 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_098 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 98 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 98 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_099 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 99 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 99 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_100 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 100 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 100 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_101 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 101 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 101 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_102 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 102 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 102 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_103 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 103 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 103 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_104 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 104 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 104 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_105 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 105 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 105 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_106 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 106 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 106 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_107 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 107 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 107 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_108 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 108 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 108 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_109 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 109 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 109 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_110 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 110 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 110 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_111 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 111 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 111 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_112 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 112 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 112 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_113 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 113 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 113 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_114 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 114 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 114 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_115 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 115 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 115 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_116 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 116 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 116 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_117 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 117 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 117 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_118 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 118 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 118 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_119 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 119 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 119 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_120 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 120 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 120 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel

theorem g32p_row07_characterBlock_121 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row07_characterValues (g32p_row07_groupNext (g32p_finBlockIndex 1944 121 r) s) = g32p_row07_characterValues (g32p_finBlockIndex 1944 121 r) * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end
