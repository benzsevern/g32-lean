import HodgeLean.Foundations.Program.G32PropFourSixPacked0101
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixFiniteCheck
import HodgeLean.Foundations.Program.G32PropFourSixArchiveReverse

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row22_groupWords : Fin 4 → List (Fin 4) :=
  ![[2, 2, 1, 1, 0, 0, 1, 2, 3, 2, 2, 0, 1, 1], [1, 1, 2, 0, 1, 1, 2, 2, 3, 3, 0, 3, 3, 1, 1, 0, 0], [1, 2, 2, 1, 0, 0, 1, 2, 2, 1, 3, 3, 0, 3, 3, 2, 2], [1, 1, 2, 2, 0, 0, 2, 2, 1, 3, 0, 0, 2, 2, 3, 1, 2, 1]]

def g32p_row22_groupMatrices : Fin 4 → HurwitzPrymRex_Mat :=
  ![![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]], ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]], ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]], ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]]

def g32p_row22_groupGenerators : Fin 4 → g32p_G :=
  fun s => g32p_archiveWord (g32p_row22_groupWords s)

def g32p_row22_groupStages_0 : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]],
   ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]],
   ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]],
   ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]],
   ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]],
   ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
   ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row22_groupCertificate_0 :
    g32p_archiveWordCertificate (g32p_row22_groupWords 0)
      g32p_row22_groupStages_0 = true := by
  decide +kernel

theorem g32p_row22_groupIntegral_0 :
    g32p_archiveIntegralWord (g32p_row22_groupWords 0) =
      g32p_row22_groupMatrices 0 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row22_groupCertificate_0
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row22_groupMatrices 0 := by
    exact ht.symm.trans (show g32p_row22_groupStages_0.headD HurwitzPrymRex_mone =
      g32p_row22_groupMatrices 0 by decide)
  exact hv.trans ha

def g32p_row22_groupStages_1 : List HurwitzPrymRex_Mat :=
  [![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]],
   ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]],
   ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]],
   ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
   ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row22_groupCertificate_1 :
    g32p_archiveWordCertificate (g32p_row22_groupWords 1)
      g32p_row22_groupStages_1 = true := by
  decide +kernel

theorem g32p_row22_groupIntegral_1 :
    g32p_archiveIntegralWord (g32p_row22_groupWords 1) =
      g32p_row22_groupMatrices 1 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row22_groupCertificate_1
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row22_groupMatrices 1 := by
    exact ht.symm.trans (show g32p_row22_groupStages_1.headD HurwitzPrymRex_mone =
      g32p_row22_groupMatrices 1 by decide)
  exact hv.trans ha

def g32p_row22_groupStages_2 : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]],
   ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]],
   ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]],
   ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
   ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
   ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row22_groupCertificate_2 :
    g32p_archiveWordCertificate (g32p_row22_groupWords 2)
      g32p_row22_groupStages_2 = true := by
  decide +kernel

theorem g32p_row22_groupIntegral_2 :
    g32p_archiveIntegralWord (g32p_row22_groupWords 2) =
      g32p_row22_groupMatrices 2 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row22_groupCertificate_2
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row22_groupMatrices 2 := by
    exact ht.symm.trans (show g32p_row22_groupStages_2.headD HurwitzPrymRex_mone =
      g32p_row22_groupMatrices 2 by decide)
  exact hv.trans ha

def g32p_row22_groupStages_3 : List HurwitzPrymRex_Mat :=
  [![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]],
   ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]],
   ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]],
   ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]],
   ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
   ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]],
   ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]],
   ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]],
   ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]],
   ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row22_groupCertificate_3 :
    g32p_archiveWordCertificate (g32p_row22_groupWords 3)
      g32p_row22_groupStages_3 = true := by
  decide +kernel

theorem g32p_row22_groupIntegral_3 :
    g32p_archiveIntegralWord (g32p_row22_groupWords 3) =
      g32p_row22_groupMatrices 3 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row22_groupCertificate_3
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row22_groupMatrices 3 := by
    exact ht.symm.trans (show g32p_row22_groupStages_3.headD HurwitzPrymRex_mone =
      g32p_row22_groupMatrices 3 by decide)
  exact hv.trans ha

theorem g32p_row22_groupGenerator_map (s : Fin 4) :
    b4b_toMatrix (g32p_row22_groupGenerators s) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
        (g32p_row22_groupMatrices s)) := by
  rw [g32p_row22_groupGenerators, g32p_archiveIntegralWord_map]
  apply congrArg (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
  fin_cases s
  · exact g32p_row22_groupIntegral_0
  · exact g32p_row22_groupIntegral_1
  · exact g32p_row22_groupIntegral_2
  · exact g32p_row22_groupIntegral_3

def g32p_row22_groupNodes : Fin 576 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
g32p_row22_Nodes00 i
else
g32p_row22_Nodes01 i)
else
(if i.val < 384 then
g32p_row22_Nodes02 i
else
(if i.val < 512 then
g32p_row22_Nodes03 i
else
g32p_row22_Nodes04 i)))


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row22_characterBlock_000 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 0 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 0 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_001 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 1 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 1 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_002 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 2 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 2 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_003 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 3 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 3 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_004 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 4 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 4 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_005 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 5 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 5 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_006 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 6 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 6 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_007 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 7 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 7 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_008 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 8 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 8 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_009 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 9 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 9 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_010 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 10 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 10 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_011 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 11 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 11 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_012 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 12 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 12 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_013 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 13 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 13 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_014 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 14 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 14 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_015 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 15 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 15 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_016 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 16 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 16 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_017 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 17 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 17 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_018 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 18 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 18 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_019 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 19 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 19 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_020 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 20 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 20 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_021 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 21 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 21 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_022 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 22 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 22 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_023 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 23 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 23 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_024 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 24 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 24 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_025 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 25 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 25 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_026 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 26 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 26 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_027 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 27 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 27 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_028 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 28 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 28 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_029 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 29 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 29 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_030 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 30 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 30 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_031 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 31 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 31 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_032 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 32 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 32 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_033 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 33 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 33 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_034 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 34 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 34 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel

theorem g32p_row22_characterBlock_035 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row22_characterValues (g32p_row22_groupNext (g32p_finBlockIndex 576 35 r) s) = g32p_row22_characterValues (g32p_finBlockIndex 576 35 r) * g32p_row22_characterValues (g32p_row22_groupNext 0 s) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end
