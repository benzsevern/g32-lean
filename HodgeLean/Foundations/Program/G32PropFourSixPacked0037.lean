import HodgeLean.Foundations.Program.G32PropFourSixPacked0033
import HodgeLean.Foundations.Program.G32PropFourSixPacked0034
import HodgeLean.Foundations.Program.G32PropFourSixPacked0035
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow03Values
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixFiniteCheck
import HodgeLean.Foundations.Program.G32PropFourSixArchiveReverse

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row03_groupWords : Fin 2 → List (Fin 4) :=
  ![[1, 0, 0, 2, 3, 0, 0, 1, 1, 2, 1, 1, 0, 0, 1], [1, 2, 2, 3, 2, 2, 0, 0, 3, 1, 2, 2, 0, 0, 3, 0, 3, 2, 1, 1, 2, 3]]

def g32p_row03_groupMatrices : Fin 2 → HurwitzPrymRex_Mat :=
  ![![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]], ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]]

def g32p_row03_groupGenerators : Fin 2 → g32p_G :=
  fun s => g32p_archiveWord (g32p_row03_groupWords s)

def g32p_row03_groupStages_0 : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
   ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row03_groupCertificate_0 :
    g32p_archiveWordCertificate (g32p_row03_groupWords 0)
      g32p_row03_groupStages_0 = true := by
  decide +kernel

theorem g32p_row03_groupIntegral_0 :
    g32p_archiveIntegralWord (g32p_row03_groupWords 0) =
      g32p_row03_groupMatrices 0 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row03_groupCertificate_0
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row03_groupMatrices 0 := by
    exact ht.symm.trans (show g32p_row03_groupStages_0.headD HurwitzPrymRex_mone =
      g32p_row03_groupMatrices 0 by decide)
  exact hv.trans ha

def g32p_row03_groupStages_1 : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]],
   ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]],
   ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]],
   ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]],
   ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]],
   ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
   ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]],
   ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]],
   ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
   ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
   ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]],
   ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
   ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
   ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
   ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
   ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
   ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
   ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_row03_groupCertificate_1 :
    g32p_archiveWordCertificate (g32p_row03_groupWords 1)
      g32p_row03_groupStages_1 = true := by
  decide +kernel

theorem g32p_row03_groupIntegral_1 :
    g32p_archiveIntegralWord (g32p_row03_groupWords 1) =
      g32p_row03_groupMatrices 1 := by
  obtain ⟨a, rest, hh, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_row03_groupCertificate_1
  have ht := congrArg (fun xs => xs.headD HurwitzPrymRex_mone) hh
  have ha : a = g32p_row03_groupMatrices 1 := by
    exact ht.symm.trans (show g32p_row03_groupStages_1.headD HurwitzPrymRex_mone =
      g32p_row03_groupMatrices 1 by decide)
  exact hv.trans ha

theorem g32p_row03_groupGenerator_map (s : Fin 2) :
    b4b_toMatrix (g32p_row03_groupGenerators s) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
        (g32p_row03_groupMatrices s)) := by
  rw [g32p_row03_groupGenerators, g32p_archiveIntegralWord_map]
  apply congrArg (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
  fin_cases s
  · exact g32p_row03_groupIntegral_0
  · exact g32p_row03_groupIntegral_1

def g32p_row03_groupNodes : Fin 4320 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 2176 then
(if i.val < 1024 then
(if i.val < 512 then
(if i.val < 256 then
(if i.val < 128 then
g32p_row03_Nodes00 i
else
g32p_row03_Nodes01 i)
else
(if i.val < 384 then
g32p_row03_Nodes02 i
else
g32p_row03_Nodes03 i))
else
(if i.val < 768 then
(if i.val < 640 then
g32p_row03_Nodes04 i
else
g32p_row03_Nodes05 i)
else
(if i.val < 896 then
g32p_row03_Nodes06 i
else
g32p_row03_Nodes07 i)))
else
(if i.val < 1536 then
(if i.val < 1280 then
(if i.val < 1152 then
g32p_row03_Nodes08 i
else
g32p_row03_Nodes09 i)
else
(if i.val < 1408 then
g32p_row03_Nodes10 i
else
g32p_row03_Nodes11 i))
else
(if i.val < 1792 then
(if i.val < 1664 then
g32p_row03_Nodes12 i
else
g32p_row03_Nodes13 i)
else
(if i.val < 1920 then
g32p_row03_Nodes14 i
else
(if i.val < 2048 then
g32p_row03_Nodes15 i
else
g32p_row03_Nodes16 i)))))
else
(if i.val < 3200 then
(if i.val < 2688 then
(if i.val < 2432 then
(if i.val < 2304 then
g32p_row03_Nodes17 i
else
g32p_row03_Nodes18 i)
else
(if i.val < 2560 then
g32p_row03_Nodes19 i
else
g32p_row03_Nodes20 i))
else
(if i.val < 2944 then
(if i.val < 2816 then
g32p_row03_Nodes21 i
else
g32p_row03_Nodes22 i)
else
(if i.val < 3072 then
g32p_row03_Nodes23 i
else
g32p_row03_Nodes24 i)))
else
(if i.val < 3712 then
(if i.val < 3456 then
(if i.val < 3328 then
g32p_row03_Nodes25 i
else
g32p_row03_Nodes26 i)
else
(if i.val < 3584 then
g32p_row03_Nodes27 i
else
g32p_row03_Nodes28 i))
else
(if i.val < 3968 then
(if i.val < 3840 then
g32p_row03_Nodes29 i
else
g32p_row03_Nodes30 i)
else
(if i.val < 4096 then
g32p_row03_Nodes31 i
else
(if i.val < 4224 then
g32p_row03_Nodes32 i
else
g32p_row03_Nodes33 i))))))


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_characterBlock_000 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 0 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 0 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_001 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 1 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 1 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_002 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 2 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 2 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_003 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 3 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 3 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_004 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 4 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 4 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_005 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 5 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 5 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_006 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 6 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 6 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_007 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 7 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 7 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_008 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 8 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 8 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_009 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 9 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 9 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_010 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 10 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 10 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_011 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 11 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 11 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_012 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 12 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 12 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_013 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 13 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 13 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_014 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 14 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 14 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_015 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 15 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 15 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_016 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 16 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 16 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_017 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 17 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 17 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_018 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 18 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 18 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_019 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 19 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 19 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_020 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 20 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 20 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_021 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 21 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 21 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_022 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 22 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 22 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_023 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 23 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 23 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_024 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 24 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 24 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_025 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 25 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 25 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_026 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 26 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 26 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_027 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 27 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 27 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_028 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 28 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 28 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_029 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 29 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 29 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_030 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 30 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 30 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_031 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 31 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 31 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_032 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 32 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 32 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_033 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 33 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 33 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_034 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 34 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 34 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_035 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 35 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 35 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_036 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 36 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 36 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_037 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 37 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 37 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_038 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 38 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 38 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_039 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 39 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 39 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_040 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 40 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 40 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_041 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 41 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 41 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_042 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 42 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 42 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_043 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 43 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 43 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_044 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 44 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 44 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_045 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 45 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 45 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_046 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 46 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 46 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_047 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 47 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 47 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_048 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 48 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 48 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_049 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 49 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 49 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_050 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 50 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 50 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_051 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 51 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 51 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_052 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 52 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 52 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_053 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 53 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 53 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_054 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 54 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 54 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_055 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 55 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 55 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_056 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 56 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 56 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_057 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 57 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 57 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_058 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 58 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 58 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_059 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 59 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 59 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_060 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 60 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 60 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_061 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 61 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 61 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_062 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 62 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 62 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_063 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 63 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 63 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
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

theorem g32p_row03_characterBlock_064 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 64 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 64 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_065 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 65 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 65 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_066 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 66 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 66 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_067 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 67 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 67 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_068 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 68 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 68 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_069 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 69 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 69 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_070 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 70 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 70 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_071 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 71 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 71 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_072 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 72 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 72 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_073 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 73 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 73 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_074 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 74 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 74 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_075 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 75 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 75 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_076 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 76 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 76 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_077 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 77 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 77 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_078 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 78 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 78 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_079 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 79 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 79 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_080 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 80 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 80 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_081 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 81 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 81 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_082 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 82 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 82 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_083 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 83 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 83 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_084 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 84 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 84 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_085 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 85 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 85 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_086 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 86 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 86 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_087 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 87 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 87 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_088 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 88 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 88 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_089 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 89 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 89 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_090 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 90 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 90 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_091 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 91 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 91 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_092 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 92 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 92 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_093 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 93 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 93 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_094 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 94 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 94 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_095 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 95 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 95 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_096 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 96 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 96 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_097 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 97 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 97 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_098 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 98 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 98 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_099 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 99 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 99 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_100 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 100 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 100 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_101 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 101 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 101 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_102 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 102 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 102 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_103 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 103 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 103 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_104 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 104 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 104 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_105 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 105 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 105 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_106 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 106 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 106 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_107 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 107 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 107 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_108 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 108 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 108 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_109 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 109 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 109 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_110 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 110 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 110 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_111 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 111 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 111 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_112 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 112 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 112 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_113 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 113 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 113 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_114 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 114 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 114 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_115 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 115 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 115 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_116 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 116 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 116 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_117 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 117 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 117 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_118 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 118 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 118 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_119 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 119 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 119 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_120 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 120 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 120 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_121 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 121 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 121 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_122 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 122 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 122 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_123 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 123 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 123 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_124 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 124 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 124 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_125 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 125 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 125 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_126 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 126 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 126 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_127 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 127 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 127 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
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

theorem g32p_row03_characterBlock_128 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 128 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 128 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_129 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 129 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 129 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_130 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 130 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 130 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_131 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 131 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 131 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_132 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 132 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 132 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_133 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 133 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 133 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_134 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 134 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 134 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_135 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 135 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 135 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_136 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 136 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 136 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_137 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 137 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 137 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_138 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 138 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 138 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_139 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 139 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 139 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_140 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 140 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 140 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_141 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 141 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 141 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_142 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 142 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 142 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_143 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 143 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 143 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_144 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 144 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 144 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_145 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 145 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 145 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_146 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 146 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 146 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_147 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 147 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 147 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_148 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 148 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 148 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_149 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 149 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 149 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_150 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 150 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 150 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_151 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 151 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 151 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_152 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 152 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 152 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_153 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 153 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 153 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_154 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 154 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 154 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_155 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 155 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 155 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_156 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 156 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 156 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_157 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 157 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 157 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_158 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 158 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 158 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_159 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 159 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 159 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_160 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 160 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 160 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_161 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 161 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 161 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_162 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 162 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 162 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_163 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 163 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 163 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_164 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 164 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 164 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_165 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 165 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 165 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_166 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 166 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 166 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_167 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 167 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 167 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_168 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 168 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 168 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_169 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 169 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 169 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_170 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 170 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 170 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_171 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 171 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 171 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_172 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 172 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 172 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_173 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 173 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 173 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_174 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 174 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 174 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_175 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 175 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 175 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_176 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 176 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 176 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_177 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 177 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 177 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_178 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 178 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 178 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_179 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 179 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 179 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_180 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 180 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 180 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_181 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 181 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 181 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_182 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 182 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 182 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_183 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 183 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 183 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_184 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 184 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 184 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_185 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 185 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 185 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_186 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 186 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 186 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_187 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 187 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 187 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_188 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 188 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 188 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_189 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 189 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 189 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_190 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 190 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 190 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_191 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 191 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 191 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
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

theorem g32p_row03_characterBlock_192 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 192 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 192 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_193 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 193 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 193 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_194 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 194 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 194 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_195 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 195 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 195 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_196 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 196 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 196 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_197 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 197 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 197 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_198 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 198 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 198 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_199 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 199 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 199 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_200 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 200 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 200 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_201 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 201 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 201 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_202 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 202 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 202 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_203 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 203 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 203 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_204 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 204 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 204 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_205 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 205 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 205 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_206 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 206 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 206 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_207 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 207 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 207 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_208 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 208 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 208 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_209 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 209 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 209 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_210 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 210 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 210 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_211 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 211 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 211 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_212 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 212 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 212 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_213 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 213 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 213 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_214 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 214 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 214 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_215 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 215 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 215 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_216 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 216 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 216 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_217 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 217 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 217 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_218 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 218 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 218 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_219 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 219 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 219 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_220 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 220 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 220 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_221 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 221 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 221 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_222 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 222 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 222 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_223 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 223 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 223 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_224 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 224 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 224 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_225 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 225 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 225 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_226 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 226 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 226 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_227 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 227 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 227 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_228 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 228 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 228 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_229 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 229 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 229 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_230 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 230 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 230 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_231 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 231 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 231 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_232 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 232 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 232 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_233 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 233 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 233 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_234 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 234 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 234 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_235 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 235 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 235 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_236 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 236 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 236 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_237 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 237 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 237 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_238 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 238 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 238 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_239 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 239 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 239 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_240 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 240 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 240 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_241 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 241 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 241 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_242 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 242 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 242 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_243 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 243 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 243 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_244 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 244 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 244 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_245 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 245 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 245 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_246 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 246 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 246 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_247 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 247 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 247 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_248 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 248 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 248 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_249 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 249 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 249 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_250 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 250 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 250 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_251 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 251 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 251 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_252 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 252 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 252 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_253 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 253 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 253 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_254 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 254 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 254 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_255 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 255 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 255 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
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

theorem g32p_row03_characterBlock_256 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 256 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 256 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_257 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 257 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 257 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_258 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 258 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 258 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_259 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 259 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 259 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_260 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 260 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 260 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_261 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 261 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 261 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_262 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 262 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 262 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_263 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 263 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 263 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_264 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 264 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 264 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_265 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 265 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 265 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_266 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 266 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 266 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_267 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 267 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 267 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_268 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 268 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 268 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel

theorem g32p_row03_characterBlock_269 : ∀ r : Fin 16, ∀ s : Fin 2, g32p_row03_characterValues (g32p_row03_groupNext (g32p_finBlockIndex 4320 269 r) s) = g32p_row03_characterValues (g32p_finBlockIndex 4320 269 r) * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end
