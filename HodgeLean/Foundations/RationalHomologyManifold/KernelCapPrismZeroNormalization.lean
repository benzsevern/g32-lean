import HodgeLean.Foundations.RationalHomologyManifold.KernelCapPrismComponents

/-! The actual stabilized kernel-prism component in target degree zero.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The first kernel-prism component retains the negative actual prism cap followed by the top boundary quotient.
Source: Bredon, Sheaf Theory, second edition, VI.12; the stabilized local kernel homotopy at the orientation cutoff.
HC no distance; AV milestone no distance.
-/
theorem kernelCapTargetPrismComponent_zero (X : TopCat.{0}) [RegularSpace X] (N : ℕ)
    (z : (SingularChainComplex ℚ X).X N) :
    kernelCapTargetPrismComponent X N z 0 ≫ (capTargetZeroTermIso X N).hom =
      -(kernelPrismCapSheafMap X N 1 N z ≫ (subdivisionLimitSheafComplex X).pOpcycles N) := by
  simp only [kernelCapTargetPrismComponent, dif_pos rfl, dite_true, Preadditive.neg_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

#print axioms kernelCapTargetPrismComponent_zero
end HodgeLean.Foundations.RationalHomologyManifold
