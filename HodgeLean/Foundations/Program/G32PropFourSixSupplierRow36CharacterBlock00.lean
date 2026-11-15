import HodgeLean.Foundations.Program.G32PropFourSixPacked0030
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixFiniteCheck
import HodgeLean.Foundations.Program.G32PropFourSixArchiveReverse

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_characterBlock_000 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 0 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 0 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_001 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 1 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 1 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_002 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 2 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 2 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_003 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 3 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 3 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_004 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 4 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 4 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_005 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 5 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 5 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_006 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 6 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 6 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_007 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 7 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 7 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_008 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 8 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 8 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_009 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 9 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 9 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_010 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 10 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 10 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_011 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 11 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 11 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_012 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 12 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 12 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_013 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 13 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 13 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_014 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 14 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 14 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_015 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 15 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 15 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_016 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 16 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 16 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_017 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 17 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 17 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_018 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 18 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 18 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_019 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 19 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 19 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_020 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 20 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 20 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_021 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 21 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 21 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_022 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 22 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 22 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel

theorem g32p_row36_characterBlock_023 : ∀ r : Fin 16, ∀ s : Fin 3, g32p_row36_characterValues (g32p_row36_groupNext (g32p_finBlockIndex 384 23 r) s) = g32p_row36_characterValues (g32p_finBlockIndex 384 23 r) * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  decide +kernel


end HodgeLean.Foundations.Program
