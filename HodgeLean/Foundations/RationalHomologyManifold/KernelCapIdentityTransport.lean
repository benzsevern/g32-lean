import HodgeLean.Foundations.RationalHomologyManifold.AmbientKernelCapRestriction
import HodgeLean.Foundations.RationalHomologyManifold.KernelSheafPrismIdentity

/-! The actual kernel cap identity in a specified total degree.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual kernel cap identity retains its stabilized prism terms when the total chain degree is specified by equality.
Source: Bredon, Sheaf Theory, second edition, VI.12; equality transport of the actual stabilized kernel cap identity.
HC no distance; AV milestone no distance.
-/
theorem kernelPrismCapSheaf_identity_cast (X : TopCat.{0}) [RegularSpace X] (N p q : ℕ)
    (z : (SingularChainComplex ℚ X).X N)
    (hz : ∀ j, (SingularChainComplex ℚ X).d N j z = 0) (hN : p + q = N) :
    (ambientLocalZeroSheafInclusion X).f p ≫ ambientFixedCapSheafMap X p q
        (((SingularChainComplex ℚ X).XIsoOfEq hN.symm).hom z) =
      -((ambientLocalZeroSheafComplex X).d p (p + 1) ≫
        (show (ambientLocalZeroSheafComplex X).X (p + 1) ⟶ (subdivisionLimitSheafComplex X).X q from
          kernelPrismCapSheafMap X N (p + 1) q z)) -
        (-1 : ℤ) ^ p • ((show (ambientLocalZeroSheafComplex X).X p ⟶ (subdivisionLimitSheafComplex X).X (q + 1) from
          kernelPrismCapSheafMap X N p (q + 1) z) ≫
          (subdivisionLimitSheafComplex X).d (q + 1) q) := by
  subst N
  change (ambientLocalZeroSheafInclusion X).f p ≫ ambientFixedCapSheafMap X p q z = _
  rw [ambientFixedCapSheafMap_kernel]
  exact kernelPrismCapSheaf_identity X p q z hz

#print axioms kernelPrismCapSheaf_identity_cast
end HodgeLean.Foundations.RationalHomologyManifold
