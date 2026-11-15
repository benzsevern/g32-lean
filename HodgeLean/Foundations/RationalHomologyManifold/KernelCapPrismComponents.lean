import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainSheafComplex
import HodgeLean.Foundations.RationalHomologyManifold.KernelSheafPrismIdentity
import HodgeLean.Foundations.RationalHomologyManifold.CapTargetZeroTerm

/-! Actual stabilized kernel-prism components in the bounded cap target.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Put the negative actual stabilized kernel prism in its bounded target degree, using the original top boundary quotient in degree zero.
Source: Bredon, Sheaf Theory, second edition, VI.12; Hatcher, Algebraic Topology, sections 2.1 and 3.3.
HC no distance; AV milestone no distance.
-/
def kernelCapTargetPrismComponent (X : TopCat.{0}) [RegularSpace X] (N : ℕ)
    (z : (SingularChainComplex ℚ X).X N) (p : ℕ) :
    (ambientLocalZeroSheafComplex X).X (p + 1) ⟶ (capTargetComplex X N).X p := by
  classical
  by_cases hp : p = 0
  · subst p
    exact -(kernelPrismCapSheafMap X N 1 N z ≫
      (subdivisionLimitSheafComplex X).pOpcycles N ≫ (capTargetZeroTermIso X N).inv)
  · by_cases hN : p ≤ N
    · exact -(kernelPrismCapSheafMap X N (p + 1) (N - p) z ≫
        (capTargetTermIso X N p (N - p) (by omega) (by omega)).inv)
    · exact 0

#print axioms kernelCapTargetPrismComponent
end HodgeLean.Foundations.RationalHomologyManifold
