import HodgeLean.Foundations.Program.G32PropFourSixPacked0102
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow22Decode
import HodgeLean.Foundations.Program.G32PropFourSixPacked0104
import HodgeLean.Foundations.Program.G32PropFourSixPacked0104
import HodgeLean.Foundations.Program.G32PropFourSixPacked0104
import HodgeLean.Foundations.Program.G32PropFourSixPacked0104
import HodgeLean.Foundations.Program.G32PropFourSixPacked0104
import HodgeLean.Foundations.Program.G32PropFourSixPacked0104
import HodgeLean.Foundations.Program.G32PropFourSixPacked0102
import HodgeLean.Foundations.Program.G32PropFourSixPacked0104
import HodgeLean.Foundations.Program.G32PropFourSixPacked0104
import HodgeLean.Foundations.Program.G32PropFourSixPacked0104
import HodgeLean.Foundations.Program.G32PropFourSixPacked0104
import HodgeLean.Foundations.Program.G32PropFourSixPacked0104
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

def g32p_row22_finiteSupplier : g32p_Supplier :=
  g32p_supplierOfFiniteTransitions (by decide) g32p_row22_groupGenerators
    g32p_row22_groupEquiv 0 g32p_row22_groupEquiv_one
    g32p_row22_groupNext g32p_row22_groupEquiv_step g32p_row22_characterValues
    (by rfl) g32p_row22_characterTransition g32p_row22_characterSurjective

theorem g32p_row22_finiteSupplier_order : Nat.card g32p_row22_finiteSupplier.H = 576 :=
  g32p_row22_groupOrder

theorem g32p_row22_finiteSupplier_value (i : Fin 576) :
    g32p_row22_finiteSupplier.χ (g32p_row22_groupEquiv i) = g32p_row22_characterValues i :=
  g32p_supplierOfFiniteTransitions_value ..

end HodgeLean.Foundations.Program
