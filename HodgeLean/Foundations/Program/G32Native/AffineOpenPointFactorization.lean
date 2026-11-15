import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineSpace
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Original points in canonical ambient affine coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- The canonical affine ring map of the original lifted point reconstructs
its original ambient point. -/
theorem affineOpenPoint_factorization (W : Over (Spec ↧ℂ))
    (U : W.left.Opens) (hU : IsAffineOpen U) (p : ComplexPoint W)
    (hp : p ∈ Point.overOpen U) :
    Spec.map (U.topIso.inv ≫ (liftToOpen W U p hp).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) ≫ hU.fromSpec = p.left := by
  rw [Spec.map_comp, Spec.map_comp, SpecMap_ΓSpecIso_hom]
  simp only [Category.assoc]
  rw [← Scheme.toSpecΓ_naturality_assoc]
  change (liftToOpen W U p hp ≫ U.toSpecΓ) ≫ hU.fromSpec = p.left
  rw [Category.assoc, ← hU.isoSpec_hom, hU.isoSpec_hom_fromSpec]
  exact liftToOpen_fac W U p hp

/-- The affine-open point map evaluates the original section at the
original ambient point. -/
theorem affineOpenPoint_sectionValue (W : Over (Spec ↧ℂ))
    (U : W.left.Opens) (p : ComplexPoint W) (hp : p ∈ Point.overOpen U)
    (r : Γ(W.left, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((liftToOpen W U p hp).appTop (U.topIso.inv r)) = Point.evaluate U r p := by
  let q := asOpenPoint W U p hp
  have hq : Point.map (openInclusion W U) q = p :=
    Over.OverMorphism.ext (liftToOpen_fac W U p hp)
  have h := evaluate_openEquiv W U (V := ⊤) (U.topIso.inv r) q
  rw [hq, evaluate_top_eq_appTop] at h
  have he := evaluate_eq (Y := W) U.ι_image_top
    ((U.ι.appIso ⊤).inv (U.topIso.inv r)) p
  rw [Scheme.Opens.ι_appIso] at he
  change Point.evaluate (U.ι ''ᵁ ⊤) (U.topIso.inv r) p =
    Point.evaluate U (U.topIso.hom (U.topIso.inv r)) p at he
  rw [Iso.inv_hom_id_apply] at he
  rw [Scheme.Opens.ι_appIso] at h
  exact h.symm.trans he

#print axioms affineOpenPoint_sectionValue
#print axioms affineOpenPoint_factorization
end HodgeLean.Foundations.Program.G32Native
