import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow27Data
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow27CharacterBlock00
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

theorem g32p_row27_characterTransition : ∀ i : Fin 486, ∀ s : Fin 3,
    g32p_row27_characterValues (g32p_row09_groupNext i s) =
      g32p_row27_characterValues i * g32p_row27_characterValues (g32p_row09_groupNext 0 s) := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row27_characterBlock_000
  · exact g32p_row27_characterBlock_001
  · exact g32p_row27_characterBlock_002
  · exact g32p_row27_characterBlock_003
  · exact g32p_row27_characterBlock_004
  · exact g32p_row27_characterBlock_005
  · exact g32p_row27_characterBlock_006
  · exact g32p_row27_characterBlock_007
  · exact g32p_row27_characterBlock_008
  · exact g32p_row27_characterBlock_009
  · exact g32p_row27_characterBlock_010
  · exact g32p_row27_characterBlock_011
  · exact g32p_row27_characterBlock_012
  · exact g32p_row27_characterBlock_013
  · exact g32p_row27_characterBlock_014
  · exact g32p_row27_characterBlock_015
  · exact g32p_row27_characterBlock_016
  · exact g32p_row27_characterBlock_017
  · exact g32p_row27_characterBlock_018
  · exact g32p_row27_characterBlock_019
  · exact g32p_row27_characterBlock_020
  · exact g32p_row27_characterBlock_021
  · exact g32p_row27_characterBlock_022
  · exact g32p_row27_characterBlock_023
  · exact g32p_row27_characterBlock_024
  · exact g32p_row27_characterBlock_025
  · exact g32p_row27_characterBlock_026
  · exact g32p_row27_characterBlock_027
  · exact g32p_row27_characterBlock_028
  · exact g32p_row27_characterBlock_029
  · exact g32p_row27_characterBlock_030

theorem g32p_row27_characterSurjective : Function.Surjective g32p_row27_characterValues := by
  decide +kernel

def g32p_row27_finiteSupplier : g32p_Supplier :=
  g32p_supplierOfFiniteTransitions (by decide) g32p_row09_groupGenerators
    g32p_row09_groupEquiv 0 g32p_row09_groupEquiv_one
    g32p_row09_groupNext g32p_row09_groupEquiv_step g32p_row27_characterValues
    (by rfl) g32p_row27_characterTransition g32p_row27_characterSurjective

theorem g32p_row27_finiteSupplier_order : Nat.card g32p_row27_finiteSupplier.H = 486 :=
  g32p_row09_groupOrder

theorem g32p_row27_finiteSupplier_value (i : Fin 486) :
    g32p_row27_finiteSupplier.χ (g32p_row09_groupEquiv i) = g32p_row27_characterValues i :=
  g32p_supplierOfFiniteTransitions_value ..

end HodgeLean.Foundations.Program
