import HodgeLean.Foundations.RationalHomologyManifold.KernelCapPrismComponents

/-! Literal formulas of the stabilized kernel-prism components in positive target degrees.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The positive bounded kernel-prism component retains the negative actual stabilized prism cap.
Source: Bredon, Sheaf Theory, second edition, VI.12; the actual stabilized kernel cap homotopy.
HC no distance; AV milestone no distance.
-/
theorem kernelCapTargetPrismComponent_positive (X : TopCat.{0}) [RegularSpace X] (N p q : ℕ)
    (z : (SingularChainComplex ℚ X).X N) (hp : 0 < p) (hN : p + q = N) :
    kernelCapTargetPrismComponent X N z p ≫ (capTargetTermIso X N p q hp hN).hom =
      -(kernelPrismCapSheafMap X N (p + 1) q z) := by
  have hq : q = N - p := by omega
  subst q
  simp only [kernelCapTargetPrismComponent, dif_neg (show p ≠ 0 by omega),
    dif_pos (show p ≤ N by omega), Preadditive.neg_comp, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

#print axioms kernelCapTargetPrismComponent_positive
end HodgeLean.Foundations.RationalHomologyManifold
