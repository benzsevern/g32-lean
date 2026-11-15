import HodgeLean.Foundations.Program.G32PropFourSixPacked0091
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow19Decode
import HodgeLean.Foundations.Program.G32PropFourSixPacked0093
import HodgeLean.Foundations.Program.G32PropFourSixPacked0093
import HodgeLean.Foundations.Program.G32PropFourSixPacked0093
import HodgeLean.Foundations.Program.G32PropFourSixPacked0093
import HodgeLean.Foundations.Program.G32PropFourSixPacked0093
import HodgeLean.Foundations.Program.G32PropFourSixPacked0093
import HodgeLean.Foundations.Program.G32PropFourSixPacked0093
import HodgeLean.Foundations.Program.G32PropFourSixPacked0093
import HodgeLean.Foundations.Program.G32PropFourSixPacked0093
import HodgeLean.Foundations.Program.G32PropFourSixPacked0093
import HodgeLean.Foundations.Program.G32PropFourSixPacked0093
import HodgeLean.Foundations.Program.G32PropFourSixPacked0091
import HodgeLean.Foundations.Program.G32PropFourSixPacked0091
import HodgeLean.Foundations.Program.G32PropFourSixPacked0093
import HodgeLean.Foundations.Program.G32PropFourSixPacked0093
import HodgeLean.Foundations.Program.G32PropFourSixPacked0093
import HodgeLean.Foundations.Program.G32PropFourSixPacked0093
import HodgeLean.Foundations.Program.G32PropFourSixPacked0093
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

def g32p_row19_finiteSupplier : g32p_Supplier :=
  g32p_supplierOfFiniteTransitions (by decide) g32p_row19_groupGenerators
    g32p_row19_groupEquiv 0 g32p_row19_groupEquiv_one
    g32p_row19_groupNext g32p_row19_groupEquiv_step g32p_row19_characterValues
    (by rfl) g32p_row19_characterTransition g32p_row19_characterSurjective

theorem g32p_row19_finiteSupplier_order : Nat.card g32p_row19_finiteSupplier.H = 1152 :=
  g32p_row19_groupOrder

theorem g32p_row19_finiteSupplier_value (i : Fin 1152) :
    g32p_row19_finiteSupplier.χ (g32p_row19_groupEquiv i) = g32p_row19_characterValues i :=
  g32p_supplierOfFiniteTransitions_value ..

end HodgeLean.Foundations.Program
