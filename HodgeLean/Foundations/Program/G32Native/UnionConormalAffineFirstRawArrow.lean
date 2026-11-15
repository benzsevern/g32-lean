import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineFirstCoordinates
import Mathlib.CategoryTheory.Comma.Arrow

/-! # The first affine conormal arrow before kernel normalization -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- The affine conormal coordinates identify the actual first arrow with its kernel map. -/
def unionConormalAffineFirstRawArrowIso
    (R : Type) [CommRing R] (A B : CommRingCat.{0})
    (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of R ⟶ B) (k : A ⟶ B)
    (h : Spec.map k ≫ Spec.map p = Spec.map q)
    (E : (ModuleCat.extendScalars (algebraMap R R)).obj
      (ModuleCat.of R (RingHom.ker p.hom)) ⟶ ModuleCat.of R (RingHom.ker q.hom))
    (hE : ∀ x : RingHom.ker p.hom, (E.hom ((1 : R) ⊗ₜ[R] x)).val = x.val) :
    Arrow.mk (unionConormalFirst (Spec.map p) (Spec.map q) (Spec.map k) h) ≅
      Arrow.mk ((tilde.functor B).map ((ModuleCat.extendScalars q.hom).map E)) := by
  have hc := unionConormal_affineComparisonMap_eq (R := R) (S := R) A B p q k
    (unionConormal_affineTriangle_identity R A B p q k h) E hE
  have hc' := (congrArg (fun u => u ≫
      (unionConormalAffineComparisonTargetIso (CommRingCat.of R) B q).hom)
      (unionConormal_affineTriangle_comparison R A B p q k h).symm).trans hc
  exact Arrow.isoMk
    (unionConormalAffineComparisonSourceIso A B p q k
      (unionConormal_affineTriangle_identity R A B p q k h))
    (unionConormalAffineComparisonTargetIso (CommRingCat.of R) B q) hc'.symm

end HodgeLean.Foundations.Program.G32Native
