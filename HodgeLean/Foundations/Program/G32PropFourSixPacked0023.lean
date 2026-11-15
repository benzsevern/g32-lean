import HodgeLean.Foundations.Program.G32PropFourSixPacked0020
import HodgeLean.Foundations.Program.G32PropFourSixPacked0021
import HodgeLean.Foundations.Program.G32PropFourSixPacked0022
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixFiniteCheck
import HodgeLean.Foundations.Program.G32PropFourSixArchiveReverse

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row02_groupWords : Fin 5 → List (Fin 4) :=
  ![[3, 0, 0, 2, 3, 1, 1, 0, 2, 2, 1, 1], [1, 1, 3, 2, 2, 0, 0, 1, 3, 0, 0, 2, 2, 1, 1, 3, 3, 0, 2, 3], [2, 0, 0, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2], [2, 2, 3, 0, 0, 3, 2, 2, 1, 0, 0, 1, 2, 2], [1, 1, 0, 1, 1, 3, 3, 0, 3, 3, 1, 1, 0, 1, 1]]

def g32p_row02_groupMatrices : Fin 5 → HurwitzPrymRex_Mat :=
  ![![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]], ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]], ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]], ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]], ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]]

def g32p_row02_groupGenerators : Fin 5 → g32p_G :=
  fun s => g32p_archiveWord (g32p_row02_groupWords s)

def g32p_row02_groupStages_0 : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
   ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]],
   ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row02_groupCertificate_0 :
    g32p_archiveWordCertificate (g32p_row02_groupWords 0)
      g32p_row02_groupStages_0 = true := by
  decide +kernel

theorem g32p_row02_groupIntegral_0 :
    g32p_archiveIntegralWord (g32p_row02_groupWords 0) =
      g32p_row02_groupMatrices 0 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row02_groupCertificate_0
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row02_groupMatrices 0 := by
    exact ht.symm.trans (show g32p_row02_groupStages_0.headD HurwitzPrymRex_mone =
      g32p_row02_groupMatrices 0 by decide)
  exact hv.trans ha

def g32p_row02_groupStages_1 : List HurwitzPrymRex_Mat :=
  [![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]],
   ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]],
   ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]],
   ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]],
   ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]],
   ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]],
   ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]],
   ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row02_groupCertificate_1 :
    g32p_archiveWordCertificate (g32p_row02_groupWords 1)
      g32p_row02_groupStages_1 = true := by
  decide +kernel

theorem g32p_row02_groupIntegral_1 :
    g32p_archiveIntegralWord (g32p_row02_groupWords 1) =
      g32p_row02_groupMatrices 1 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row02_groupCertificate_1
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row02_groupMatrices 1 := by
    exact ht.symm.trans (show g32p_row02_groupStages_1.headD HurwitzPrymRex_mone =
      g32p_row02_groupMatrices 1 by decide)
  exact hv.trans ha

def g32p_row02_groupStages_2 : List HurwitzPrymRex_Mat :=
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

theorem g32p_row02_groupCertificate_2 :
    g32p_archiveWordCertificate (g32p_row02_groupWords 2)
      g32p_row02_groupStages_2 = true := by
  decide +kernel

theorem g32p_row02_groupIntegral_2 :
    g32p_archiveIntegralWord (g32p_row02_groupWords 2) =
      g32p_row02_groupMatrices 2 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row02_groupCertificate_2
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row02_groupMatrices 2 := by
    exact ht.symm.trans (show g32p_row02_groupStages_2.headD HurwitzPrymRex_mone =
      g32p_row02_groupMatrices 2 by decide)
  exact hv.trans ha

def g32p_row02_groupStages_3 : List HurwitzPrymRex_Mat :=
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

theorem g32p_row02_groupCertificate_3 :
    g32p_archiveWordCertificate (g32p_row02_groupWords 3)
      g32p_row02_groupStages_3 = true := by
  decide +kernel

theorem g32p_row02_groupIntegral_3 :
    g32p_archiveIntegralWord (g32p_row02_groupWords 3) =
      g32p_row02_groupMatrices 3 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row02_groupCertificate_3
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row02_groupMatrices 3 := by
    exact ht.symm.trans (show g32p_row02_groupStages_3.headD HurwitzPrymRex_mone =
      g32p_row02_groupMatrices 3 by decide)
  exact hv.trans ha

def g32p_row02_groupStages_4 : List HurwitzPrymRex_Mat :=
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

theorem g32p_row02_groupCertificate_4 :
    g32p_archiveWordCertificate (g32p_row02_groupWords 4)
      g32p_row02_groupStages_4 = true := by
  decide +kernel

theorem g32p_row02_groupIntegral_4 :
    g32p_archiveIntegralWord (g32p_row02_groupWords 4) =
      g32p_row02_groupMatrices 4 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row02_groupCertificate_4
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row02_groupMatrices 4 := by
    exact ht.symm.trans (show g32p_row02_groupStages_4.headD HurwitzPrymRex_mone =
      g32p_row02_groupMatrices 4 by decide)
  exact hv.trans ha

theorem g32p_row02_groupGenerator_map (s : Fin 5) :
    b4b_toMatrix (g32p_row02_groupGenerators s) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
        (g32p_row02_groupMatrices s)) := by
  rw [g32p_row02_groupGenerators, g32p_archiveIntegralWord_map]
  apply congrArg (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
  fin_cases s
  · exact g32p_row02_groupIntegral_0
  · exact g32p_row02_groupIntegral_1
  · exact g32p_row02_groupIntegral_2
  · exact g32p_row02_groupIntegral_3
  · exact g32p_row02_groupIntegral_4

def g32p_row02_groupNodes : Fin 3456 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 1664 then
(if i.val < 768 then
(if i.val < 384 then
(if i.val < 128 then
g32p_row02_Nodes00 i
else
(if i.val < 256 then
g32p_row02_Nodes01 i
else
g32p_row02_Nodes02 i))
else
(if i.val < 512 then
g32p_row02_Nodes03 i
else
(if i.val < 640 then
g32p_row02_Nodes04 i
else
g32p_row02_Nodes05 i)))
else
(if i.val < 1152 then
(if i.val < 896 then
g32p_row02_Nodes06 i
else
(if i.val < 1024 then
g32p_row02_Nodes07 i
else
g32p_row02_Nodes08 i))
else
(if i.val < 1408 then
(if i.val < 1280 then
g32p_row02_Nodes09 i
else
g32p_row02_Nodes10 i)
else
(if i.val < 1536 then
g32p_row02_Nodes11 i
else
g32p_row02_Nodes12 i))))
else
(if i.val < 2560 then
(if i.val < 2048 then
(if i.val < 1792 then
g32p_row02_Nodes13 i
else
(if i.val < 1920 then
g32p_row02_Nodes14 i
else
g32p_row02_Nodes15 i))
else
(if i.val < 2304 then
(if i.val < 2176 then
g32p_row02_Nodes16 i
else
g32p_row02_Nodes17 i)
else
(if i.val < 2432 then
g32p_row02_Nodes18 i
else
g32p_row02_Nodes19 i)))
else
(if i.val < 2944 then
(if i.val < 2688 then
g32p_row02_Nodes20 i
else
(if i.val < 2816 then
g32p_row02_Nodes21 i
else
g32p_row02_Nodes22 i))
else
(if i.val < 3200 then
(if i.val < 3072 then
g32p_row02_Nodes23 i
else
g32p_row02_Nodes24 i)
else
(if i.val < 3328 then
g32p_row02_Nodes25 i
else
g32p_row02_Nodes26 i)))))


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_characterBlock_000 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 0 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 0 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_001 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 1 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 1 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_002 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 2 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 2 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_003 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 3 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 3 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_004 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 4 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 4 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_005 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 5 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 5 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_006 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 6 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 6 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_007 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 7 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 7 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_008 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 8 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 8 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_009 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 9 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 9 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_010 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 10 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 10 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_011 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 11 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 11 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_012 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 12 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 12 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_013 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 13 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 13 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_014 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 14 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 14 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_015 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 15 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 15 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_016 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 16 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 16 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_017 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 17 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 17 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_018 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 18 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 18 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_019 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 19 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 19 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_020 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 20 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 20 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_021 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 21 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 21 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_022 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 22 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 22 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_023 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 23 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 23 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_024 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 24 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 24 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_025 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 25 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 25 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_026 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 26 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 26 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_027 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 27 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 27 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_028 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 28 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 28 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_029 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 29 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 29 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_030 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 30 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 30 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_031 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 31 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 31 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_032 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 32 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 32 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_033 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 33 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 33 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_034 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 34 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 34 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_035 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 35 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 35 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_036 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 36 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 36 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_037 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 37 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 37 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_038 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 38 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 38 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_039 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 39 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 39 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_040 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 40 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 40 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_041 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 41 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 41 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_042 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 42 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 42 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_043 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 43 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 43 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_044 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 44 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 44 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_045 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 45 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 45 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_046 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 46 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 46 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_047 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 47 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 47 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_048 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 48 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 48 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_049 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 49 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 49 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_050 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 50 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 50 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_051 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 51 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 51 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_052 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 52 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 52 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_053 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 53 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 53 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_054 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 54 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 54 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_055 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 55 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 55 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_056 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 56 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 56 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_057 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 57 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 57 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_058 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 58 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 58 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_059 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 59 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 59 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_060 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 60 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 60 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_061 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 61 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 61 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_062 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 62 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 62 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_063 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 63 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 63 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
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

theorem g32p_row02_characterBlock_064 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 64 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 64 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_065 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 65 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 65 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_066 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 66 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 66 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_067 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 67 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 67 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_068 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 68 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 68 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_069 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 69 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 69 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_070 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 70 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 70 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_071 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 71 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 71 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_072 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 72 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 72 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_073 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 73 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 73 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_074 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 74 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 74 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_075 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 75 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 75 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_076 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 76 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 76 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_077 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 77 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 77 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_078 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 78 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 78 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_079 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 79 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 79 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_080 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 80 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 80 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_081 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 81 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 81 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_082 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 82 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 82 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_083 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 83 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 83 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_084 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 84 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 84 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_085 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 85 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 85 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_086 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 86 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 86 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_087 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 87 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 87 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_088 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 88 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 88 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_089 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 89 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 89 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_090 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 90 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 90 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_091 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 91 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 91 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_092 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 92 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 92 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_093 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 93 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 93 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_094 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 94 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 94 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_095 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 95 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 95 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_096 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 96 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 96 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_097 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 97 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 97 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_098 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 98 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 98 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_099 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 99 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 99 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_100 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 100 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 100 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_101 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 101 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 101 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_102 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 102 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 102 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_103 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 103 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 103 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_104 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 104 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 104 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_105 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 105 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 105 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_106 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 106 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 106 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_107 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 107 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 107 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_108 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 108 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 108 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_109 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 109 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 109 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_110 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 110 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 110 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_111 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 111 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 111 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_112 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 112 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 112 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_113 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 113 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 113 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_114 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 114 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 114 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_115 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 115 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 115 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_116 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 116 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 116 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_117 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 117 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 117 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_118 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 118 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 118 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_119 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 119 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 119 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_120 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 120 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 120 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_121 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 121 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 121 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_122 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 122 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 122 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_123 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 123 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 123 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_124 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 124 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 124 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_125 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 125 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 125 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_126 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 126 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 126 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_127 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 127 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 127 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
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

theorem g32p_row02_characterBlock_128 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 128 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 128 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_129 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 129 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 129 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_130 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 130 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 130 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_131 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 131 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 131 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_132 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 132 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 132 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_133 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 133 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 133 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_134 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 134 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 134 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_135 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 135 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 135 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_136 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 136 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 136 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_137 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 137 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 137 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_138 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 138 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 138 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_139 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 139 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 139 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_140 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 140 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 140 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_141 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 141 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 141 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_142 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 142 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 142 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_143 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 143 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 143 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_144 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 144 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 144 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_145 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 145 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 145 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_146 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 146 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 146 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_147 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 147 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 147 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_148 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 148 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 148 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_149 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 149 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 149 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_150 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 150 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 150 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_151 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 151 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 151 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_152 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 152 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 152 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_153 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 153 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 153 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_154 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 154 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 154 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_155 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 155 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 155 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_156 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 156 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 156 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_157 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 157 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 157 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_158 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 158 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 158 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_159 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 159 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 159 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_160 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 160 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 160 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_161 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 161 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 161 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_162 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 162 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 162 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_163 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 163 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 163 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_164 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 164 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 164 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_165 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 165 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 165 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_166 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 166 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 166 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_167 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 167 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 167 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_168 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 168 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 168 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_169 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 169 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 169 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_170 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 170 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 170 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_171 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 171 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 171 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_172 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 172 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 172 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_173 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 173 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 173 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_174 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 174 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 174 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_175 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 175 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 175 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_176 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 176 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 176 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_177 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 177 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 177 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_178 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 178 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 178 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_179 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 179 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 179 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_180 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 180 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 180 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_181 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 181 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 181 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_182 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 182 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 182 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_183 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 183 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 183 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_184 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 184 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 184 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_185 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 185 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 185 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_186 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 186 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 186 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_187 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 187 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 187 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_188 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 188 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 188 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_189 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 189 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 189 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_190 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 190 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 190 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_191 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 191 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 191 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
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

theorem g32p_row02_characterBlock_192 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 192 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 192 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_193 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 193 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 193 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_194 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 194 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 194 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_195 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 195 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 195 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_196 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 196 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 196 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_197 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 197 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 197 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_198 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 198 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 198 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_199 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 199 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 199 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_200 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 200 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 200 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_201 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 201 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 201 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_202 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 202 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 202 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_203 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 203 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 203 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_204 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 204 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 204 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_205 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 205 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 205 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_206 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 206 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 206 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_207 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 207 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 207 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_208 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 208 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 208 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_209 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 209 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 209 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_210 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 210 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 210 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_211 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 211 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 211 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_212 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 212 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 212 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_213 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 213 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 213 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_214 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 214 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 214 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel

theorem g32p_row02_characterBlock_215 : ∀ r : Fin 16, ∀ s : Fin 5, g32p_row02_characterValues (g32p_row02_groupNext (g32p_finBlockIndex 3456 215 r) s) = g32p_row02_characterValues (g32p_finBlockIndex 3456 215 r) * g32p_row02_characterValues (g32p_row02_groupNext 0 s) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end
