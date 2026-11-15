import HodgeConjecture.Mathlib.AlgebraicGeometry.Over.Basic

/-! # Original scalar structures in morphisms of section algebras -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The original section map of a morphism over the base is a map of the
original section algebras, retaining the specified inverse-image open. -/
def overSpecSectionMap {A : Type} [CommRing A]
    {Q W : Over (Spec ↧A)} (i : Q ⟶ W) (U : W.left.Opens) :
    letI := overSpecAlgebra W U
    letI := overSpecAlgebra Q (i.left ⁻¹ᵁ U)
    Γ(W.left, U) →ₐ[A] Γ(Q.left, i.left ⁻¹ᵁ U) := by
  letI := overSpecAlgebra W U
  letI := overSpecAlgebra Q (i.left ⁻¹ᵁ U)
  refine { toRingHom := (i.left.app U).hom, commutes' := ?_ }
  intro a
  have h : W.hom.appLE ⊤ U (by simp) ≫ i.left.app U =
      Q.hom.appLE ⊤ (i.left ⁻¹ᵁ U) (by simp) := by
    rw [i.left.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Over.w i]
  exact congrArg (fun f : Γ(Spec ↧A, ⊤) ⟶ Γ(Q.left, i.left ⁻¹ᵁ U) =>
    f ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) h

#print axioms overSpecSectionMap
end HodgeLean.Foundations.Program.G32Native
