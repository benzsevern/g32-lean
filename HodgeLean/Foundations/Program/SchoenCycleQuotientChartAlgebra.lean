import HodgeLean.Foundations.Program.SchoenCycleStep1SectionAction

/-! # The quotient-linear action on an actual inverse-image chart -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Pullback by a morphism over the quotient is an algebra endomorphism over the
actual base chart ring.
Source: Hartshorne, Algebraic Geometry, II.2, functoriality of regular sections. -/
def s2e_quotient_chartPullbackAlgHom
    (X Y : Over (Spec ↧ℂ)) (q : X ⟶ Y) (u : X ⟶ X) (hu : u ≫ q = q)
    (U : Y.left.Opens) :
    letI : Algebra Γ(Y.left, U) Γ(X.left, q.left ⁻¹ᵁ U) := (q.left.app U).hom.toAlgebra
    Γ(X.left, q.left ⁻¹ᵁ U) →ₐ[Γ(Y.left, U)] Γ(X.left, q.left ⁻¹ᵁ U) := by
  let W := q.left ⁻¹ᵁ U
  letI : Algebra Γ(Y.left, U) Γ(X.left, W) := (q.left.app U).hom.toAlgebra
  let ρ := u.left.appLE W W (s2e_step1_action_preimage X Y q u hu U)
  have he : q.left.app U ≫ ρ = q.left.app U := by
    dsimp only [ρ]
    rw [q.left.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    have hu' : u.left ≫ q.left = q.left := congrArg Over.Hom.left hu
    simp only [hu', W]
  refine { ρ.hom with commutes' := ?_ }
  intro r
  exact congrArg (fun t : Γ(Y.left, U) ⟶ Γ(X.left, W) => t.hom r) he

#print axioms s2e_quotient_chartPullbackAlgHom
end HodgeLean.Foundations.Program
