import HodgeLean.Foundations.Program.G32PropFourSixPacked0082
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow17Values
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixFiniteCheck
import HodgeLean.Foundations.Program.G32PropFourSixArchiveReverse

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row17_groupWords : Fin 4 → List (Fin 4) :=
  ![[1, 2, 2, 0, 0, 1, 1, 3, 0, 1, 2, 2], [1, 2, 2, 1, 1, 0, 1, 1, 2, 2, 3, 3, 0, 3, 3, 2, 2, 1, 0, 0], [1, 2, 2, 1, 2, 2, 0, 1, 1, 0, 2, 3, 3, 0, 3, 3, 2, 2, 1, 0, 0], [1, 3, 2, 2, 3, 0, 1, 2, 2, 1, 0, 0, 2, 2, 1, 1]]

def g32p_row17_groupMatrices : Fin 4 → HurwitzPrymRex_Mat :=
  ![![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]], ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]], ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]]

def g32p_row17_groupGenerators : Fin 4 → g32p_G :=
  fun s => g32p_archiveWord (g32p_row17_groupWords s)

def g32p_row17_groupStages_0 : List HurwitzPrymRex_Mat :=
  [![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]],
   ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]],
   ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row17_groupCertificate_0 :
    g32p_archiveWordCertificate (g32p_row17_groupWords 0)
      g32p_row17_groupStages_0 = true := by
  decide +kernel

theorem g32p_row17_groupIntegral_0 :
    g32p_archiveIntegralWord (g32p_row17_groupWords 0) =
      g32p_row17_groupMatrices 0 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row17_groupCertificate_0
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row17_groupMatrices 0 := by
    exact ht.symm.trans (show g32p_row17_groupStages_0.headD HurwitzPrymRex_mone =
      g32p_row17_groupMatrices 0 by decide)
  exact hv.trans ha

def g32p_row17_groupStages_1 : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]],
   ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
   ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]],
   ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]],
   ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]],
   ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row17_groupCertificate_1 :
    g32p_archiveWordCertificate (g32p_row17_groupWords 1)
      g32p_row17_groupStages_1 = true := by
  decide +kernel

theorem g32p_row17_groupIntegral_1 :
    g32p_archiveIntegralWord (g32p_row17_groupWords 1) =
      g32p_row17_groupMatrices 1 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row17_groupCertificate_1
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row17_groupMatrices 1 := by
    exact ht.symm.trans (show g32p_row17_groupStages_1.headD HurwitzPrymRex_mone =
      g32p_row17_groupMatrices 1 by decide)
  exact hv.trans ha

def g32p_row17_groupStages_2 : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]],
   ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]],
   ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]],
   ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]],
   ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]],
   ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]],
   ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
   ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]],
   ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]],
   ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]],
   ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row17_groupCertificate_2 :
    g32p_archiveWordCertificate (g32p_row17_groupWords 2)
      g32p_row17_groupStages_2 = true := by
  decide +kernel

theorem g32p_row17_groupIntegral_2 :
    g32p_archiveIntegralWord (g32p_row17_groupWords 2) =
      g32p_row17_groupMatrices 2 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row17_groupCertificate_2
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row17_groupMatrices 2 := by
    exact ht.symm.trans (show g32p_row17_groupStages_2.headD HurwitzPrymRex_mone =
      g32p_row17_groupMatrices 2 by decide)
  exact hv.trans ha

def g32p_row17_groupStages_3 : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row17_groupCertificate_3 :
    g32p_archiveWordCertificate (g32p_row17_groupWords 3)
      g32p_row17_groupStages_3 = true := by
  decide +kernel

theorem g32p_row17_groupIntegral_3 :
    g32p_archiveIntegralWord (g32p_row17_groupWords 3) =
      g32p_row17_groupMatrices 3 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row17_groupCertificate_3
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row17_groupMatrices 3 := by
    exact ht.symm.trans (show g32p_row17_groupStages_3.headD HurwitzPrymRex_mone =
      g32p_row17_groupMatrices 3 by decide)
  exact hv.trans ha

theorem g32p_row17_groupGenerator_map (s : Fin 4) :
    b4b_toMatrix (g32p_row17_groupGenerators s) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
        (g32p_row17_groupMatrices s)) := by
  rw [g32p_row17_groupGenerators, g32p_archiveIntegralWord_map]
  apply congrArg (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
  fin_cases s
  · exact g32p_row17_groupIntegral_0
  · exact g32p_row17_groupIntegral_1
  · exact g32p_row17_groupIntegral_2
  · exact g32p_row17_groupIntegral_3

def g32p_row17_groupNodes : Fin 1296 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 640 then
(if i.val < 256 then
(if i.val < 128 then
g32p_row17_Nodes00 i
else
g32p_row17_Nodes01 i)
else
(if i.val < 384 then
g32p_row17_Nodes02 i
else
(if i.val < 512 then
g32p_row17_Nodes03 i
else
g32p_row17_Nodes04 i)))
else
(if i.val < 1024 then
(if i.val < 768 then
g32p_row17_Nodes05 i
else
(if i.val < 896 then
g32p_row17_Nodes06 i
else
g32p_row17_Nodes07 i))
else
(if i.val < 1152 then
g32p_row17_Nodes08 i
else
(if i.val < 1280 then
g32p_row17_Nodes09 i
else
g32p_row17_Nodes10 i))))


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row17_characterBlock_000 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 0 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 0 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_001 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 1 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 1 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_002 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 2 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 2 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_003 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 3 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 3 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_004 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 4 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 4 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_005 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 5 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 5 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_006 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 6 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 6 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_007 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 7 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 7 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_008 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 8 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 8 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_009 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 9 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 9 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_010 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 10 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 10 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_011 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 11 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 11 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_012 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 12 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 12 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_013 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 13 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 13 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_014 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 14 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 14 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_015 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 15 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 15 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_016 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 16 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 16 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_017 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 17 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 17 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_018 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 18 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 18 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_019 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 19 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 19 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_020 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 20 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 20 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_021 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 21 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 21 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_022 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 22 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 22 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_023 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 23 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 23 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_024 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 24 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 24 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_025 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 25 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 25 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_026 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 26 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 26 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_027 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 27 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 27 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_028 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 28 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 28 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_029 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 29 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 29 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_030 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 30 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 30 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_031 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 31 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 31 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_032 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 32 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 32 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_033 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 33 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 33 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_034 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 34 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 34 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_035 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 35 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 35 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_036 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 36 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 36 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_037 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 37 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 37 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_038 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 38 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 38 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_039 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 39 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 39 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_040 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 40 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 40 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_041 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 41 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 41 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_042 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 42 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 42 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_043 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 43 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 43 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_044 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 44 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 44 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_045 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 45 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 45 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_046 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 46 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 46 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_047 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 47 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 47 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_048 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 48 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 48 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_049 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 49 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 49 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_050 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 50 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 50 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_051 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 51 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 51 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_052 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 52 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 52 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_053 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 53 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 53 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_054 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 54 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 54 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_055 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 55 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 55 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_056 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 56 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 56 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_057 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 57 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 57 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_058 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 58 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 58 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_059 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 59 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 59 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_060 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 60 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 60 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_061 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 61 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 61 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_062 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 62 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 62 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_063 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 63 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 63 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
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

theorem g32p_row17_characterBlock_064 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 64 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 64 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_065 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 65 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 65 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_066 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 66 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 66 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_067 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 67 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 67 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_068 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 68 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 68 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_069 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 69 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 69 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_070 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 70 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 70 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_071 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 71 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 71 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_072 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 72 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 72 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_073 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 73 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 73 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_074 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 74 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 74 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_075 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 75 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 75 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_076 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 76 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 76 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_077 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 77 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 77 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_078 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 78 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 78 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_079 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 79 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 79 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel

theorem g32p_row17_characterBlock_080 : ∀ r : Fin 16, ∀ s : Fin 4, g32p_row17_characterValues (g32p_row17_groupNext (g32p_finBlockIndex 1296 80 r) s) = g32p_row17_characterValues (g32p_finBlockIndex 1296 80 r) * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end
