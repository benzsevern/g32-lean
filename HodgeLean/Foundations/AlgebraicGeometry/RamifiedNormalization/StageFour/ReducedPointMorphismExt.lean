import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Basic

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- On a reduced complex scheme, equality at every complex point detects equality of morphisms to a separated complex scheme. -/
theorem reduced_complex_morphism_ext
    (X Y : Over (Spec ↧ℂ)) [IsReduced X.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom]
    (f g : X ⟶ Y) (h : ∀ p : ComplexPoint X, Point.map f p = Point.map g p) : f = g := by
  apply Over.OverMorphism.ext
  haveI : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  apply ext_of_apply_eq Y.hom Set.univ isClosed_univ.isLocallyClosed dense_univ
    (H' := f.w.trans g.w.symm)
  intro x _ hx
  let p : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom x hx)
    (pointOfClosedPoint_comp X.hom x hx)
  have hp := congrArg (fun q : ComplexPoint Y => q.left (IsLocalRing.closedPoint ℂ)) (h p)
  change f.left (pointOfClosedPoint X.hom x hx (IsLocalRing.closedPoint ℂ)) =
    g.left (pointOfClosedPoint X.hom x hx (IsLocalRing.closedPoint ℂ)) at hp
  simpa only [pointOfClosedPoint_apply] using hp

end AlgebraicGeometry.RamifiedNormalization.StageFour
