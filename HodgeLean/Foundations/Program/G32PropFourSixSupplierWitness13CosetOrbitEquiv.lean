import HodgeLean.Foundations.Program.G32PropFourSixPacked1070
import HodgeLean.Foundations.Program.G32PropFourSixPacked0634
import HodgeLean.Foundations.Program.G32PropFourSixPacked0634

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

def g32p_row13_cosetEquiv : Fin 6480 ≃ (g32p_G ⧸ g32p_row13_finiteSupplier.H) :=
  Equiv.ofBijective _ g32p_row13_cosetEnumeration

end HodgeLean.Foundations.Program
