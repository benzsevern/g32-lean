import HodgeLean.Foundations.RationalHomologyManifold.AmbientFixedCycleCapComplex
import HodgeLean.Foundations.RationalHomologyManifold.KernelCapPrismNormalization
import HodgeLean.Foundations.RationalHomologyManifold.KernelCapIdentityTransport

/-! The actual bounded kernel cap homotopy in interior degrees.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual bounded kernel-prism components satisfy the cap homotopy identity in every interior degree above one.
Source: Bredon, Sheaf Theory, second edition, VI.12; Hatcher, Algebraic Topology, sections 2.1 and 3.3.
HC no distance; AV milestone no distance.
-/
theorem kernelCapTargetPrismComponent_interior (X : TopCat.{0}) [RegularSpace X] (N p q : ℕ)
    (z : (SingularChainComplex ℚ X).X N)
    (hz : ∀ j, (SingularChainComplex ℚ X).d N j z = 0)
    (hp : 0 < p) (hN : p + 1 + q = N) :
    (ambientLocalZeroSheafInclusion X).f (p + 1) ≫ ambientCapTargetComponent X N z (p + 1) =
      (ambientLocalZeroSheafComplex X).d (p + 1) (p + 2) ≫ kernelCapTargetPrismComponent X N z (p + 1) +
        kernelCapTargetPrismComponent X N z p ≫ (capTargetComplex X N).d p (p + 1) := by
  let B := ambientLocalZeroSheafComplex X
  let C := subdivisionLimitSheafComplex X
  let e := capTargetTermIso X N (p + 1) q (by omega) hN
  let e' := capTargetTermIso X N p (q + 1) hp (by omega)
  let u : B.X (p + 2) ⟶ C.X q := kernelPrismCapSheafMap X N (p + 2) q z
  let v : B.X (p + 1) ⟶ C.X (q + 1) := kernelPrismCapSheafMap X N (p + 1) (q + 1) z
  have hnext : kernelCapTargetPrismComponent X N z (p + 1) ≫ e.hom = -u :=
    kernelCapTargetPrismComponent_positive X N (p + 1) q z (by omega) hN
  have hprev : kernelCapTargetPrismComponent X N z p ≫ e'.hom = -v :=
    kernelCapTargetPrismComponent_positive X N p (q + 1) z hp (by omega)
  have hbd := congrArg (fun f => kernelCapTargetPrismComponent X N z p ≫ f)
    (capTargetTermIso_boundary X N p q hp (by omega))
  have hbd' : (kernelCapTargetPrismComponent X N z p ≫ (capTargetComplex X N).d p (p + 1)) ≫ e.hom =
      (-1 : ℤ) ^ (p + 1) • ((-v) ≫ C.d (q + 1) q) := by
    have hh : (kernelCapTargetPrismComponent X N z p ≫ (capTargetComplex X N).d p (p + 1)) ≫ e.hom =
        (-1 : ℤ) ^ (p + 1) • ((kernelCapTargetPrismComponent X N z p ≫ e'.hom) ≫ C.d (q + 1) q) := by
      simpa only [Category.assoc, Preadditive.comp_zsmul] using hbd
    rw [hprev] at hh
    exact hh
  apply (cancel_mono e.hom).mp
  calc
    _ = (ambientLocalZeroSheafInclusion X).f (p + 1) ≫ ambientFixedCapSheafMap X (p + 1) q
        (((SingularChainComplex ℚ X).XIsoOfEq hN.symm).hom z) := by
      rw [Category.assoc, ambientCapTargetComponent_positive X N (p + 1) q z (by omega) hN]
    _ = -(B.d (p + 1) (p + 2) ≫ u) - (-1 : ℤ) ^ (p + 1) • (v ≫ C.d (q + 1) q) :=
      kernelPrismCapSheaf_identity_cast X N (p + 1) q z hz hN
    _ = _ := by
      rw [Preadditive.add_comp, Category.assoc, hnext, hbd']
      simp only [Preadditive.comp_neg, Preadditive.neg_comp, smul_neg, sub_eq_add_neg]
      rfl

#print axioms kernelCapTargetPrismComponent_interior
end HodgeLean.Foundations.RationalHomologyManifold
