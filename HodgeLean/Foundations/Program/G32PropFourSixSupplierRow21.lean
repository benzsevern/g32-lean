import HodgeLean.Foundations.Program.G32PropFourSixPacked0097
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow21Decode
import HodgeLean.Foundations.Program.G32PropFourSixPacked0099
import HodgeLean.Foundations.Program.G32PropFourSixPacked0099
import HodgeLean.Foundations.Program.G32PropFourSixPacked0099
import HodgeLean.Foundations.Program.G32PropFourSixPacked0099
import HodgeLean.Foundations.Program.G32PropFourSixPacked0099
import HodgeLean.Foundations.Program.G32PropFourSixPacked0099
import HodgeLean.Foundations.Program.G32PropFourSixPacked0099
import HodgeLean.Foundations.Program.G32PropFourSixPacked0097
import HodgeLean.Foundations.Program.G32PropFourSixPacked0099
import HodgeLean.Foundations.Program.G32PropFourSixPacked0099
import HodgeLean.Foundations.Program.G32PropFourSixPacked0099
import HodgeLean.Foundations.Program.G32PropFourSixPacked0099
import HodgeLean.Foundations.Program.G32PropFourSixPacked0099
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

def g32p_row21_finiteSupplier : g32p_Supplier :=
  g32p_supplierOfFiniteTransitions (by decide) g32p_row21_groupGenerators
    g32p_row21_groupEquiv 0 g32p_row21_groupEquiv_one
    g32p_row21_groupNext g32p_row21_groupEquiv_step g32p_row21_characterValues
    (by rfl) g32p_row21_characterTransition g32p_row21_characterSurjective

theorem g32p_row21_finiteSupplier_order : Nat.card g32p_row21_finiteSupplier.H = 972 :=
  g32p_row21_groupOrder

theorem g32p_row21_finiteSupplier_value (i : Fin 972) :
    g32p_row21_finiteSupplier.χ (g32p_row21_groupEquiv i) = g32p_row21_characterValues i :=
  g32p_supplierOfFiniteTransitions_value ..

end HodgeLean.Foundations.Program
