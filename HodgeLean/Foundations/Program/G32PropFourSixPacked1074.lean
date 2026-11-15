import HodgeLean.Foundations.Program.G32PropFourSixPacked1073
import HodgeLean.Foundations.Program.G32PropFourSixPacked1070
import HodgeLean.Foundations.Program.G32PropFourSixPacked0634
import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness13CosetOrbitEquiv

section

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

def g32p_row13_cosetOrbitEquiv2 : Fin 3312 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 2)) (g32p_G ⧸ g32p_row13_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 2) g32p_row13_cosetEquiv
    (g32p_row13_cosetBranchNext 2) (g32p_row13_cosetQuotientStep 2) g32p_row13_cosetLabels2 g32p_row13_cosetRoots2
    g32p_row13_cosetDistances2 g32p_row13_cosetRootLabels2 g32p_row13_cosetNextLabels2 g32p_row13_cosetReach2)

end HodgeLean.Foundations.Program

end
end
