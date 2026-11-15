import HodgeLean.Foundations.Program.G32PropFourSixPacked0084
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow17Decode
import HodgeLean.Foundations.Program.G32PropFourSixPacked0086
import HodgeLean.Foundations.Program.G32PropFourSixPacked0086
import HodgeLean.Foundations.Program.G32PropFourSixPacked0086
import HodgeLean.Foundations.Program.G32PropFourSixPacked0086
import HodgeLean.Foundations.Program.G32PropFourSixPacked0086
import HodgeLean.Foundations.Program.G32PropFourSixPacked0086
import HodgeLean.Foundations.Program.G32PropFourSixPacked0086
import HodgeLean.Foundations.Program.G32PropFourSixPacked0086
import HodgeLean.Foundations.Program.G32PropFourSixPacked0086
import HodgeLean.Foundations.Program.G32PropFourSixPacked0086
import HodgeLean.Foundations.Program.G32PropFourSixPacked0086
import HodgeLean.Foundations.Program.G32PropFourSixPacked0086
import HodgeLean.Foundations.Program.G32PropFourSixPacked0084
import HodgeLean.Foundations.Program.G32PropFourSixPacked0084
import HodgeLean.Foundations.Program.G32PropFourSixPacked0086
import HodgeLean.Foundations.Program.G32PropFourSixPacked0086
import HodgeLean.Foundations.Program.G32PropFourSixPacked0086
import HodgeLean.Foundations.Program.G32PropFourSixPacked0086
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

theorem g32p_row17_characterTransition : ∀ i : Fin 1296, ∀ s : Fin 4,
    g32p_row17_characterValues (g32p_row17_groupNext i s) =
      g32p_row17_characterValues i * g32p_row17_characterValues (g32p_row17_groupNext 0 s) := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row17_characterBlock_000
  · exact g32p_row17_characterBlock_001
  · exact g32p_row17_characterBlock_002
  · exact g32p_row17_characterBlock_003
  · exact g32p_row17_characterBlock_004
  · exact g32p_row17_characterBlock_005
  · exact g32p_row17_characterBlock_006
  · exact g32p_row17_characterBlock_007
  · exact g32p_row17_characterBlock_008
  · exact g32p_row17_characterBlock_009
  · exact g32p_row17_characterBlock_010
  · exact g32p_row17_characterBlock_011
  · exact g32p_row17_characterBlock_012
  · exact g32p_row17_characterBlock_013
  · exact g32p_row17_characterBlock_014
  · exact g32p_row17_characterBlock_015
  · exact g32p_row17_characterBlock_016
  · exact g32p_row17_characterBlock_017
  · exact g32p_row17_characterBlock_018
  · exact g32p_row17_characterBlock_019
  · exact g32p_row17_characterBlock_020
  · exact g32p_row17_characterBlock_021
  · exact g32p_row17_characterBlock_022
  · exact g32p_row17_characterBlock_023
  · exact g32p_row17_characterBlock_024
  · exact g32p_row17_characterBlock_025
  · exact g32p_row17_characterBlock_026
  · exact g32p_row17_characterBlock_027
  · exact g32p_row17_characterBlock_028
  · exact g32p_row17_characterBlock_029
  · exact g32p_row17_characterBlock_030
  · exact g32p_row17_characterBlock_031
  · exact g32p_row17_characterBlock_032
  · exact g32p_row17_characterBlock_033
  · exact g32p_row17_characterBlock_034
  · exact g32p_row17_characterBlock_035
  · exact g32p_row17_characterBlock_036
  · exact g32p_row17_characterBlock_037
  · exact g32p_row17_characterBlock_038
  · exact g32p_row17_characterBlock_039
  · exact g32p_row17_characterBlock_040
  · exact g32p_row17_characterBlock_041
  · exact g32p_row17_characterBlock_042
  · exact g32p_row17_characterBlock_043
  · exact g32p_row17_characterBlock_044
  · exact g32p_row17_characterBlock_045
  · exact g32p_row17_characterBlock_046
  · exact g32p_row17_characterBlock_047
  · exact g32p_row17_characterBlock_048
  · exact g32p_row17_characterBlock_049
  · exact g32p_row17_characterBlock_050
  · exact g32p_row17_characterBlock_051
  · exact g32p_row17_characterBlock_052
  · exact g32p_row17_characterBlock_053
  · exact g32p_row17_characterBlock_054
  · exact g32p_row17_characterBlock_055
  · exact g32p_row17_characterBlock_056
  · exact g32p_row17_characterBlock_057
  · exact g32p_row17_characterBlock_058
  · exact g32p_row17_characterBlock_059
  · exact g32p_row17_characterBlock_060
  · exact g32p_row17_characterBlock_061
  · exact g32p_row17_characterBlock_062
  · exact g32p_row17_characterBlock_063
  · exact g32p_row17_characterBlock_064
  · exact g32p_row17_characterBlock_065
  · exact g32p_row17_characterBlock_066
  · exact g32p_row17_characterBlock_067
  · exact g32p_row17_characterBlock_068
  · exact g32p_row17_characterBlock_069
  · exact g32p_row17_characterBlock_070
  · exact g32p_row17_characterBlock_071
  · exact g32p_row17_characterBlock_072
  · exact g32p_row17_characterBlock_073
  · exact g32p_row17_characterBlock_074
  · exact g32p_row17_characterBlock_075
  · exact g32p_row17_characterBlock_076
  · exact g32p_row17_characterBlock_077
  · exact g32p_row17_characterBlock_078
  · exact g32p_row17_characterBlock_079
  · exact g32p_row17_characterBlock_080

theorem g32p_row17_characterSurjective : Function.Surjective g32p_row17_characterValues := by
  decide +kernel


end HodgeLean.Foundations.Program
