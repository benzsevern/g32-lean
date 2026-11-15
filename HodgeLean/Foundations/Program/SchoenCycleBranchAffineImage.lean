import HodgeLean.Foundations.Program.SchoenCycleInsertionImmersion

/-! # Affine kernels for the actual retained branch image -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- On each actual affine quotient chart, the retained branch image ideal is
the section-ring kernel of the actual marked branch composite.
Source: Mathlib, AlgebraicGeometry.Scheme.Hom.ker_apply;
Hartshorne, Algebraic Geometry, II.5. -/
theorem s2e_branchIdeal_affine_kernel
    (Z B : Over (Spec ↧ℂ)) [IsProjective Z.hom] (n : ℕ)
    (γ : g3_power Z (n + 1) ⟶ B) [IsFinite γ.left]
    (a : ComplexPoint Z) (U : B.left.affineOpens) :
    (s2c_branchIdeal Z B n γ a).ideal U =
      RingHom.ker ((s2c_branchInsertion Z n a ≫ γ).left.app U.1).hom := by
  let q := s2c_branchInsertion Z n a
  letI : IsClosedImmersion q.left := s2e_branchInsertion_isClosedImmersion Z n a
  change (q.left ≫ γ.left).ker.ideal U = RingHom.ker ((q.left ≫ γ.left).app U.1).hom
  exact (q.left ≫ γ.left).ker_apply U

end HodgeLean.Foundations.Program
