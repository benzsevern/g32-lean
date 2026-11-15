import HodgeLean.Foundations.Program.SchoenTowerI2aActualBranchSections

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- The elementary coefficient equations persist through the actual square
of restricted quotient maps and section pullbacks.
Source: Hartshorne, Algebraic Geometry, II.2, functoriality of affine sections. -/
theorem s2v_i2a_symmetric_coefficient_restriction
    (U V U' V' : Over (Spec ↧ℂ)) (q : V ⟶ U) (q' : V' ⟶ U')
    (rU : U' ⟶ U) (rV : V' ⟶ V) (hsquare : rV ≫ q = q' ≫ rU)
    (n : ℕ) (z : Fin n → Γ(V.left, ⊤)) (c : Fin n → Γ(U.left, ⊤))
    (hc : ∀ j, q.left.appTop.hom (c j) = MvPolynomial.aeval (R := ℂ) z
      (MvPolynomial.esymm (Fin n) ℂ (j.val + 1))) :
    ∀ j, q'.left.appTop.hom (rU.left.appTop.hom (c j)) =
      MvPolynomial.aeval (R := ℂ) (fun i => rV.left.appTop.hom (z i))
        (MvPolynomial.esymm (Fin n) ℂ (j.val + 1)) := by
  intro j
  have H := congrArg (fun f : V' ⟶ U => f.left.appTop.hom (c j)) hsquare
  simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at H
  rw [← H, hc]
  exact MvPolynomial.comp_aeval_apply z (s2t_overSectionsAlgHom rV) _

end HodgeLean.Foundations.Program
