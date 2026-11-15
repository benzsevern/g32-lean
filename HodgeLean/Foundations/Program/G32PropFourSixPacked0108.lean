import HodgeLean.Foundations.Program.G32PropFourSixPacked0107
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixFiniteCheck
import HodgeLean.Foundations.Program.G32PropFourSixArchiveReverse

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row24_groupWords : Fin 4 → List (Fin 4) :=
  ![[1, 1, 0, 0, 3, 2, 2, 3, 2, 1, 1, 0, 1, 1, 2, 2, 1], [0, 1, 3, 0, 0, 2, 3, 0, 1, 1, 2, 1], [1, 0, 0, 1, 3, 3, 0, 3, 3], [1, 1, 0, 1, 1, 3, 3, 0, 3, 3, 1, 1, 0, 1, 1]]

def g32p_row24_groupMatrices : Fin 4 → HurwitzPrymRex_Mat :=
  ![![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]], ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]], ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]]

def g32p_row24_groupGenerators : Fin 4 → g32p_G :=
  fun s => g32p_archiveWord (g32p_row24_groupWords s)

def g32p_row24_groupStages_0 : List HurwitzPrymRex_Mat :=
  [![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
   ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
   ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
   ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]],
   ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
   ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
   ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row24_groupCertificate_0 :
    g32p_archiveWordCertificate (g32p_row24_groupWords 0)
      g32p_row24_groupStages_0 = true := by
  decide +kernel

theorem g32p_row24_groupIntegral_0 :
    g32p_archiveIntegralWord (g32p_row24_groupWords 0) =
      g32p_row24_groupMatrices 0 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row24_groupCertificate_0
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row24_groupMatrices 0 := by
    exact ht.symm.trans (show g32p_row24_groupStages_0.headD HurwitzPrymRex_mone =
      g32p_row24_groupMatrices 0 by decide)
  exact hv.trans ha

def g32p_row24_groupStages_1 : List HurwitzPrymRex_Mat :=
  [![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]],
   ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]],
   ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row24_groupCertificate_1 :
    g32p_archiveWordCertificate (g32p_row24_groupWords 1)
      g32p_row24_groupStages_1 = true := by
  decide +kernel

theorem g32p_row24_groupIntegral_1 :
    g32p_archiveIntegralWord (g32p_row24_groupWords 1) =
      g32p_row24_groupMatrices 1 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row24_groupCertificate_1
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row24_groupMatrices 1 := by
    exact ht.symm.trans (show g32p_row24_groupStages_1.headD HurwitzPrymRex_mone =
      g32p_row24_groupMatrices 1 by decide)
  exact hv.trans ha

def g32p_row24_groupStages_2 : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]],
   ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]],
   ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
   ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row24_groupCertificate_2 :
    g32p_archiveWordCertificate (g32p_row24_groupWords 2)
      g32p_row24_groupStages_2 = true := by
  decide +kernel

theorem g32p_row24_groupIntegral_2 :
    g32p_archiveIntegralWord (g32p_row24_groupWords 2) =
      g32p_row24_groupMatrices 2 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row24_groupCertificate_2
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row24_groupMatrices 2 := by
    exact ht.symm.trans (show g32p_row24_groupStages_2.headD HurwitzPrymRex_mone =
      g32p_row24_groupMatrices 2 by decide)
  exact hv.trans ha

def g32p_row24_groupStages_3 : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]],
   ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]],
   ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]],
   ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
   ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row24_groupCertificate_3 :
    g32p_archiveWordCertificate (g32p_row24_groupWords 3)
      g32p_row24_groupStages_3 = true := by
  decide +kernel

theorem g32p_row24_groupIntegral_3 :
    g32p_archiveIntegralWord (g32p_row24_groupWords 3) =
      g32p_row24_groupMatrices 3 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row24_groupCertificate_3
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row24_groupMatrices 3 := by
    exact ht.symm.trans (show g32p_row24_groupStages_3.headD HurwitzPrymRex_mone =
      g32p_row24_groupMatrices 3 by decide)
  exact hv.trans ha

theorem g32p_row24_groupGenerator_map (s : Fin 4) :
    b4b_toMatrix (g32p_row24_groupGenerators s) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
        (g32p_row24_groupMatrices s)) := by
  rw [g32p_row24_groupGenerators, g32p_archiveIntegralWord_map]
  apply congrArg (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
  fin_cases s
  · exact g32p_row24_groupIntegral_0
  · exact g32p_row24_groupIntegral_1
  · exact g32p_row24_groupIntegral_2
  · exact g32p_row24_groupIntegral_3

def g32p_row24_groupNodes : Fin 1152 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 512 then
(if i.val < 256 then
(if i.val < 128 then
g32p_row24_Nodes00 i
else
g32p_row24_Nodes01 i)
else
(if i.val < 384 then
g32p_row24_Nodes02 i
else
g32p_row24_Nodes03 i))
else
(if i.val < 768 then
(if i.val < 640 then
g32p_row24_Nodes04 i
else
g32p_row24_Nodes05 i)
else
(if i.val < 896 then
g32p_row24_Nodes06 i
else
(if i.val < 1024 then
g32p_row24_Nodes07 i
else
g32p_row24_Nodes08 i))))


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row24_characterBlock_000 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 0 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 0 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_001 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 1 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 1 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_002 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 2 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 2 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_003 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 3 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 3 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_004 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 4 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 4 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_005 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 5 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 5 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_006 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 6 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 6 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_007 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 7 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 7 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_008 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 8 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 8 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_009 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 9 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 9 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_010 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 10 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 10 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_011 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 11 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 11 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_012 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 12 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 12 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_013 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 13 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 13 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_014 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 14 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 14 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_015 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 15 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 15 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_016 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 16 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 16 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_017 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 17 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 17 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_018 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 18 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 18 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_019 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 19 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 19 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_020 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 20 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 20 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_021 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 21 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 21 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_022 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 22 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 22 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_023 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 23 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 23 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_024 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 24 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 24 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_025 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 25 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 25 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_026 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 26 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 26 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_027 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 27 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 27 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_028 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 28 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 28 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_029 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 29 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 29 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_030 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 30 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 30 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_031 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 31 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 31 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_032 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 32 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 32 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_033 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 33 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 33 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_034 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 34 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 34 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_035 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 35 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 35 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_036 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 36 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 36 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_037 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 37 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 37 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_038 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 38 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 38 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_039 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 39 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 39 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_040 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 40 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 40 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_041 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 41 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 41 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_042 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 42 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 42 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_043 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 43 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 43 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_044 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 44 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 44 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_045 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 45 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 45 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_046 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 46 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 46 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_047 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 47 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 47 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_048 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 48 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 48 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_049 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 49 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 49 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_050 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 50 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 50 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_051 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 51 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 51 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_052 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 52 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 52 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_053 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 53 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 53 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_054 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 54 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 54 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_055 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 55 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 55 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_056 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 56 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 56 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_057 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 57 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 57 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_058 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 58 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 58 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_059 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 59 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 59 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_060 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 60 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 60 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_061 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 61 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 61 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_062 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 62 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 62 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_063 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 63 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 63 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
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

theorem g32p_row24_characterBlock_064 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 64 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 64 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_065 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 65 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 65 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_066 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 66 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 66 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_067 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 67 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 67 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_068 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 68 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 68 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_069 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 69 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 69 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_070 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 70 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 70 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel

theorem g32p_row24_characterBlock_071 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row24_characterValues (g32p_row24_groupNext (g32p_finBlockIndex 1152 71 r) s) = g32p_row24_characterValues (g32p_finBlockIndex 1152 71 r) * g32p_row24_characterValues (g32p_row24_groupNext 0 s) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end
