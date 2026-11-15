import HodgeLean.Foundations.Program.G32PropFourSixPacked0057
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow07Decode
import HodgeLean.Foundations.Program.G32PropFourSixPacked0059
import HodgeLean.Foundations.Program.G32PropFourSixPacked0059
import HodgeLean.Foundations.Program.G32PropFourSixPacked0059
import HodgeLean.Foundations.Program.G32PropFourSixPacked0059
import HodgeLean.Foundations.Program.G32PropFourSixPacked0059
import HodgeLean.Foundations.Program.G32PropFourSixPacked0059
import HodgeLean.Foundations.Program.G32PropFourSixPacked0059
import HodgeLean.Foundations.Program.G32PropFourSixPacked0059
import HodgeLean.Foundations.Program.G32PropFourSixPacked0059
import HodgeLean.Foundations.Program.G32PropFourSixPacked0059
import HodgeLean.Foundations.Program.G32PropFourSixPacked0059
import HodgeLean.Foundations.Program.G32PropFourSixPacked0059
import HodgeLean.Foundations.Program.G32PropFourSixPacked0059
import HodgeLean.Foundations.Program.G32PropFourSixPacked0059
import HodgeLean.Foundations.Program.G32PropFourSixPacked0057
import HodgeLean.Foundations.Program.G32PropFourSixPacked0057
import HodgeLean.Foundations.Program.G32PropFourSixPacked0059
import HodgeLean.Foundations.Program.G32PropFourSixPacked0059
import HodgeLean.Foundations.Program.G32PropFourSixPacked0060
import HodgeLean.Foundations.Program.G32PropFourSixPacked0060
import HodgeLean.Foundations.Program.G32PropFourSixPacked0060
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

def g32p_row07_finiteSupplier : g32p_Supplier :=
  g32p_supplierOfFiniteTransitions (by decide) g32p_row07_groupGenerators
    g32p_row07_groupEquiv 0 g32p_row07_groupEquiv_one
    g32p_row07_groupNext g32p_row07_groupEquiv_step g32p_row07_characterValues
    (by rfl) g32p_row07_characterTransition g32p_row07_characterSurjective

theorem g32p_row07_finiteSupplier_order : Nat.card g32p_row07_finiteSupplier.H = 1944 :=
  g32p_row07_groupOrder

theorem g32p_row07_finiteSupplier_value (i : Fin 1944) :
    g32p_row07_finiteSupplier.χ (g32p_row07_groupEquiv i) = g32p_row07_characterValues i :=
  g32p_supplierOfFiniteTransitions_value ..

end HodgeLean.Foundations.Program
