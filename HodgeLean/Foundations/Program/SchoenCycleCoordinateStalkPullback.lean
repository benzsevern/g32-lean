import Mathlib.AlgebraicGeometry.Stalk

/-! # Actual coordinate section germs under polynomial-spectrum maps -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A scheme morphism defined by global coordinates pulls their localized
stalk values back to the actual germs of those coordinate sections.
Source: Hartshorne, Algebraic Geometry, II.2; Mathlib,
AlgebraicGeometry.ΓSpecIso_inv_ΓSpec_adjunction_homEquiv. -/
theorem s2e_coordinate_stalk_pullback
    (Y : Scheme) (P : CommRingCat) (e : P ⟶ Γ(Y, ⊤)) (x : Y) (r : P) :
    let f := Y.toSpecΓ ≫ Spec.map e
    f.stalkMap x (StructureSheaf.toStalk P (f x) r) = Y.presheaf.germ ⊤ x trivial (e r) := by
  let f := Y.toSpecΓ ≫ Spec.map e
  have hΓ : (Scheme.ΓSpecIso P).inv ≫ f.appTop = e :=
    ΓSpecIso_inv_ΓSpec_adjunction_homEquiv e
  have he : StructureSheaf.toStalk P (f x) ≫ f.stalkMap x =
      e ≫ Y.presheaf.germ ⊤ x trivial := by
    change ((Scheme.ΓSpecIso P).inv ≫ (Spec P).presheaf.germ ⊤ (f x) trivial) ≫
      f.stalkMap x = _
    rw [Category.assoc, f.germ_stalkMap, ← Category.assoc, hΓ]
    simp only [TopologicalSpace.Opens.map_top]
  exact congrArg (fun k : P ⟶ Y.presheaf.stalk x => k.hom r) he

end HodgeLean.Foundations.Program
