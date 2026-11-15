import HodgeLean.Foundations.Program.G32PropFourSixPacked0045
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow04Decode
import HodgeLean.Foundations.Program.G32PropFourSixPacked0047
import HodgeLean.Foundations.Program.G32PropFourSixPacked0047
import HodgeLean.Foundations.Program.G32PropFourSixPacked0047
import HodgeLean.Foundations.Program.G32PropFourSixPacked0047
import HodgeLean.Foundations.Program.G32PropFourSixPacked0047
import HodgeLean.Foundations.Program.G32PropFourSixPacked0047
import HodgeLean.Foundations.Program.G32PropFourSixPacked0047
import HodgeLean.Foundations.Program.G32PropFourSixPacked0047
import HodgeLean.Foundations.Program.G32PropFourSixPacked0047
import HodgeLean.Foundations.Program.G32PropFourSixPacked0047
import HodgeLean.Foundations.Program.G32PropFourSixPacked0047
import HodgeLean.Foundations.Program.G32PropFourSixPacked0047
import HodgeLean.Foundations.Program.G32PropFourSixPacked0047
import HodgeLean.Foundations.Program.G32PropFourSixPacked0045
import HodgeLean.Foundations.Program.G32PropFourSixPacked0045
import HodgeLean.Foundations.Program.G32PropFourSixPacked0047
import HodgeLean.Foundations.Program.G32PropFourSixPacked0047
import HodgeLean.Foundations.Program.G32PropFourSixPacked0047
import HodgeLean.Foundations.Program.G32PropFourSixPacked0048
import HodgeLean.Foundations.Program.G32PropFourSixPacked0048
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

def g32p_row04_finiteSupplier : g32p_Supplier :=
  g32p_supplierOfFiniteTransitions (by decide) g32p_row04_groupGenerators
    g32p_row04_groupEquiv 0 g32p_row04_groupEquiv_one
    g32p_row04_groupNext g32p_row04_groupEquiv_step g32p_row04_characterValues
    (by rfl) g32p_row04_characterTransition g32p_row04_characterSurjective

theorem g32p_row04_finiteSupplier_order : Nat.card g32p_row04_finiteSupplier.H = 1728 :=
  g32p_row04_groupOrder

theorem g32p_row04_finiteSupplier_value (i : Fin 1728) :
    g32p_row04_finiteSupplier.χ (g32p_row04_groupEquiv i) = g32p_row04_characterValues i :=
  g32p_supplierOfFiniteTransitions_value ..

end HodgeLean.Foundations.Program
