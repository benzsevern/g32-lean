import HodgeLean.Foundations.Program.G32Native.AffineOpenPointFactorization

/-! # Original immersion points on an ambient affine open -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- The original source point lies in the inverse image of every ambient
open containing its original image. -/
theorem immersionPoint_mem_preimage {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W)
    (U : W.left.Opens) (x : ComplexPoint Q) (hx : Point.map i x ∈ Point.overOpen U) :
    x ∈ Point.overOpen (i.left ⁻¹ᵁ U) := by
  change i.left x.underlying ∈ U
  exact (show (Point.map i x).underlying ∈ U from hx)

/-- The original source point in the restricted immersion maps to the
specified affine point whenever that point reconstructs its original image. -/
theorem affineOpenImmersionPoint_factorization {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W)
    (U : W.left.Opens) (hU : IsAffineOpen U) (x : ComplexPoint Q)
    (hx : Point.map i x ∈ Point.overOpen U)
    (ε : Γ(W.left, U) ⟶ CommRingCat.of ℂ)
    (hε : Spec.map ε ≫ hU.fromSpec = (Point.map i x).left) :
    liftToOpen Q (i.left ⁻¹ᵁ U) x (immersionPoint_mem_preimage i U x hx) ≫
      ((i.left ∣_ U) ≫ hU.isoSpec.hom) = Spec.map ε := by
  apply (cancel_mono hU.fromSpec).mp
  rw [Category.assoc, Category.assoc, hU.isoSpec_hom_fromSpec,
    morphismRestrict_ι, ← Category.assoc, liftToOpen_fac]
  exact hε.symm

#print axioms affineOpenImmersionPoint_factorization
#print axioms immersionPoint_mem_preimage
end HodgeLean.Foundations.Program.G32Native
