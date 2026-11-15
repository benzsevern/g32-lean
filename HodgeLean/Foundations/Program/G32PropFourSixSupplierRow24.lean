import HodgeLean.Foundations.Program.G32PropFourSixPacked0108
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow24Decode
import HodgeLean.Foundations.Program.G32PropFourSixPacked0110
import HodgeLean.Foundations.Program.G32PropFourSixPacked0110
import HodgeLean.Foundations.Program.G32PropFourSixPacked0110
import HodgeLean.Foundations.Program.G32PropFourSixPacked0110
import HodgeLean.Foundations.Program.G32PropFourSixPacked0110
import HodgeLean.Foundations.Program.G32PropFourSixPacked0110
import HodgeLean.Foundations.Program.G32PropFourSixPacked0110
import HodgeLean.Foundations.Program.G32PropFourSixPacked0110
import HodgeLean.Foundations.Program.G32PropFourSixPacked0110
import HodgeLean.Foundations.Program.G32PropFourSixPacked0110
import HodgeLean.Foundations.Program.G32PropFourSixPacked0110
import HodgeLean.Foundations.Program.G32PropFourSixPacked0108
import HodgeLean.Foundations.Program.G32PropFourSixPacked0108
import HodgeLean.Foundations.Program.G32PropFourSixPacked0110
import HodgeLean.Foundations.Program.G32PropFourSixPacked0110
import HodgeLean.Foundations.Program.G32PropFourSixPacked0110
import HodgeLean.Foundations.Program.G32PropFourSixPacked0110
import HodgeLean.Foundations.Program.G32PropFourSixPacked0110
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

def g32p_row24_finiteSupplier : g32p_Supplier :=
  g32p_supplierOfFiniteTransitions (by decide) g32p_row24_groupGenerators
    g32p_row24_groupEquiv 0 g32p_row24_groupEquiv_one
    g32p_row24_groupNext g32p_row24_groupEquiv_step g32p_row24_characterValues
    (by rfl) g32p_row24_characterTransition g32p_row24_characterSurjective

theorem g32p_row24_finiteSupplier_order : Nat.card g32p_row24_finiteSupplier.H = 1152 :=
  g32p_row24_groupOrder

theorem g32p_row24_finiteSupplier_value (i : Fin 1152) :
    g32p_row24_finiteSupplier.χ (g32p_row24_groupEquiv i) = g32p_row24_characterValues i :=
  g32p_supplierOfFiniteTransitions_value ..

end HodgeLean.Foundations.Program
