import HodgeLean.Foundations.RationalHomologyManifold.AmbientFixedCapSheaf

/-! Differential compatibility of the actual ambient fixed-cycle cap after sheafification.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The sheafified literal fixed-cycle cap retains the ambient coboundary and the original signed supported-chain boundary.
Source: Bredon, Sheaf Theory, second edition, I.1 and VI.12; Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance.
-/
theorem ambientFixedCapSheafMap_coboundary (X : TopCat.{0}) (p q : ℕ)
    (z : (SingularChainComplex ℚ X).X (p + q + 1)) (hz : boundary ℚ (p + q) z = 0) :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).map
        ((ambientCochainPresheafComplex X).d p (p + 1)) ≫
      ambientFixedCapSheafMap X (p + 1) q (reassocChain ℚ p q z) =
    (-1 : ℤ) ^ (p + 1) • (ambientFixedCapSheafMap X p (q + 1) z ≫
      (subdivisionLimitSheafComplex X).d (q + 1) q) := by
  apply (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).map_injective
  apply sheafify_hom_ext (Opens.grothendieckTopology X) _ _ ((subdivisionLimitSheafComplex X).X q).property
  change toSheafify _ _ ≫ (sheafifyMap _ _ ≫ (ambientFixedCapSheafMap X (p + 1) q _).hom) =
    toSheafify _ _ ≫ ((-1 : ℤ) ^ (p + 1) • ((ambientFixedCapSheafMap X p (q + 1) z).hom ≫
      ((subdivisionLimitSheafComplex X).d (q + 1) q).hom))
  simp only [Preadditive.comp_zsmul]
  rw [← Category.assoc, ← toSheafify_naturality]
  simp only [Category.assoc, ambientFixedCapSheafMap, toSheafify_sheafifyLift]
  rw [← Category.assoc, toSheafify_sheafifyLift]
  exact ambientFixedCapPresheafMap_coboundary X p q z hz

#print axioms ambientFixedCapSheafMap_coboundary
end HodgeLean.Foundations.RationalHomologyManifold
