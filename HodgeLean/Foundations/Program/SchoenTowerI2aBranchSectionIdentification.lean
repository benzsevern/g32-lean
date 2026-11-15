import HodgeLean.Foundations.Program.SchoenTowerI2aBranchSectionRestriction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- The actual restricted branch section is the specified descended branch
coordinate when their products agree through the injective quotient map.
Source: Hartshorne, Algebraic Geometry, II.2, section pullback and affine descent. -/
theorem s2v_i2a_branch_section_restriction_identification
    (U V U' V' : Over (Spec ↧ℂ)) (q : V ⟶ U) (q' : V' ⟶ U')
    (rU : U' ⟶ U) (rV : V' ⟶ V) (hsquare : rV ≫ q = q' ≫ rU)
    (hqinj : Function.Injective q'.left.appTop.hom)
    (n : ℕ) (z : Fin n → Γ(V.left, ⊤)) (b : ℂ)
    (f : Γ(U.left, ⊤)) (f' : Γ(U'.left, ⊤))
    (hf : q.left.appTop.hom f = ∏ i, (algebraMap ℂ Γ(V.left, ⊤) b - z i))
    (hf' : q'.left.appTop.hom f' =
      ∏ i, (algebraMap ℂ Γ(V'.left, ⊤) b - rV.left.appTop.hom (z i))) :
    rU.left.appTop.hom f = f' := by
  apply hqinj
  have H := congrArg (fun k : V' ⟶ U => k.left.appTop.hom f) hsquare
  simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at H
  rw [← H, hf, hf', map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_sub]
  exact congrArg (fun a => a - rV.left.appTop.hom (z i))
    ((s2t_overSectionsAlgHom rV).commutes b)

end HodgeLean.Foundations.Program
