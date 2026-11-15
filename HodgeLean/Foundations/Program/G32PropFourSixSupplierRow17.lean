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
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow17Character
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

def g32p_row17_finiteSupplier : g32p_Supplier :=
  g32p_supplierOfFiniteTransitions (by decide) g32p_row17_groupGenerators
    g32p_row17_groupEquiv 0 g32p_row17_groupEquiv_one
    g32p_row17_groupNext g32p_row17_groupEquiv_step g32p_row17_characterValues
    (by rfl) g32p_row17_characterTransition g32p_row17_characterSurjective

theorem g32p_row17_finiteSupplier_order : Nat.card g32p_row17_finiteSupplier.H = 1296 :=
  g32p_row17_groupOrder

theorem g32p_row17_finiteSupplier_value (i : Fin 1296) :
    g32p_row17_finiteSupplier.χ (g32p_row17_groupEquiv i) = g32p_row17_characterValues i :=
  g32p_supplierOfFiniteTransitions_value ..

end HodgeLean.Foundations.Program
