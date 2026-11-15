import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineFirstRawArrow
import HodgeLean.Foundations.Program.G32Native.UnionConormalIdealKernelArrowIso

/-! # The affine first arrow in intersection ideal coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual affine first arrow identifies with extension of ideal inclusion. -/
def unionConormalAffineFirstIdealArrowIso
    (R : Type) [CommRing R] (A B : CommRingCat.{0})
    (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of R ⟶ B) (k : A ⟶ B)
    (h : Spec.map k ≫ Spec.map p = Spec.map q) (J : Ideal R)
    (hP : RingHom.ker p.hom = RingHom.ker q.hom ⊓ J) :
    Arrow.mk (unionConormalFirst (Spec.map p) (Spec.map q) (Spec.map k) h) ≅
      Arrow.mk ((tilde.functor B).map ((ModuleCat.extendScalars q.hom).map
        (ModuleCat.ofHom (Submodule.inclusion
          (show RingHom.ker q.hom ⊓ J ≤ RingHom.ker q.hom from inf_le_left))))) := by
  exact unionConormalAffineFirstRawArrowIso R A B p q k h
      (unionConormalIdealKernelArrow p.hom q.hom J hP)
      (unionConormalIdealKernelArrow_one p.hom q.hom J hP) ≪≫
    (tilde.functor B).mapArrow.mapIso
      (unionConormalIdealKernelArrowIso p.hom q.hom J hP)

end HodgeLean.Foundations.Program.G32Native
