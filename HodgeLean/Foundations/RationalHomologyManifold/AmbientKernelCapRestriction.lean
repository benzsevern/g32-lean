import HodgeLean.Foundations.RationalHomologyManifold.AmbientKernelSheafInclusion
import HodgeLean.Foundations.RationalHomologyManifold.AmbientFixedCapSheaf
import HodgeLean.Foundations.RationalHomologyManifold.KernelFixedCapSheaf

/-! Literal restriction of ambient fixed-chain cap to the actual sheafified kernel.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Restricting the actual ambient cap sheaf morphism is the previously constructed actual kernel cap morphism.
Source: Bredon, Sheaf Theory, second edition, I.1 and VI.12; uniqueness in the sheafification universal property.
HC no distance; AV milestone no distance.
-/
theorem ambientFixedCapSheafMap_kernel (X : TopCat.{0}) (p q : ℕ)
    (z : (SingularChainComplex ℚ X).X (p + q)) :
    (ambientLocalZeroSheafInclusion X).f p ≫ ambientFixedCapSheafMap X p q z =
      kernelFixedCapSheafMap X p q z := by
  apply (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).map_injective
  apply sheafify_hom_ext (Opens.grothendieckTopology X) _ _ ((subdivisionLimitSheafComplex X).X q).property
  change toSheafify _ _ ≫ (sheafifyMap _ _ ≫ (ambientFixedCapSheafMap X p q z).hom) =
    toSheafify _ _ ≫ (kernelFixedCapSheafMap X p q z).hom
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
  simp only [ambientFixedCapSheafMap, kernelFixedCapSheafMap, toSheafify_sheafifyLift]

#print axioms ambientFixedCapSheafMap_kernel
end HodgeLean.Foundations.RationalHomologyManifold
