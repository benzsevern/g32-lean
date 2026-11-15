import HodgeLean.Foundations.RationalHomologyManifold.KernelFixedCapSheaf

/-! The actual kernel prism-cap identity after sheafification.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The sheafified fixed-cycle cap on the actual kernel is the signed sum of its two sheafified stabilized prism caps.
Source: Bredon, Sheaf Theory, second edition, I.1 and VI.12; sheafification of the actual kernel homotopy identity.
HC no distance; AV milestone no distance.
-/
theorem kernelPrismCapSheaf_identity (X : TopCat.{0}) [RegularSpace X] (p q : ℕ)
    (z : (SingularChainComplex ℚ X).X (p + q))
    (hz : ∀ j, (SingularChainComplex ℚ X).d (p + q) j z = 0) :
    kernelFixedCapSheafMap X p q z =
      -((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).map
          ((ambientLocalZeroPresheafComplex X).d p (p + 1)) ≫
        kernelPrismCapSheafMap X (p + q) (p + 1) q z) -
      (-1 : ℤ) ^ p • (kernelPrismCapSheafMap X (p + q) p (q + 1) z ≫
        (subdivisionLimitSheafComplex X).d (q + 1) q) := by
  apply (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).map_injective
  apply sheafify_hom_ext (Opens.grothendieckTopology X) _ _ ((subdivisionLimitSheafComplex X).X q).property
  change toSheafify _ _ ≫ (kernelFixedCapSheafMap X p q z).hom = _
  rw [show (kernelFixedCapSheafMap X p q z).hom =
      sheafifyLift (Opens.grothendieckTopology X)
        ((kernel.ι (ambientCochainPresheafComplexRestriction X)).f p ≫ ambientFixedCapPresheafMap X p q z)
        ((subdivisionLimitSheafComplex X).X q).property from rfl,
    toSheafify_sheafifyLift]
  change _ = toSheafify (Opens.grothendieckTopology X) _ ≫
    (-(sheafifyMap (Opens.grothendieckTopology X) ((ambientLocalZeroPresheafComplex X).d p (p + 1)) ≫
      (kernelPrismCapSheafMap X (p + q) (p + 1) q z).hom) -
      (-1 : ℤ) ^ p • ((kernelPrismCapSheafMap X (p + q) p (q + 1) z).hom ≫
        ((subdivisionLimitSheafComplex X).d (q + 1) q).hom))
  simp only [Preadditive.comp_sub, Preadditive.comp_neg, Preadditive.comp_zsmul]
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    kernelPrismCapSheafMap_unit, ← Category.assoc, kernelPrismCapSheafMap_unit]
  exact kernelPrismCapPresheaf_identity X p q z hz

#print axioms kernelPrismCapSheaf_identity
end HodgeLean.Foundations.RationalHomologyManifold
