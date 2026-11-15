import HodgeLean.Foundations.Program.SchoenCycleBranchCompositeStalk

/-! # Actual branch sections in the marked parameter ideal -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Every actual branch image ideal section pulls back into the marked
parameter ideal at every actual insertion point.
Source: Hartshorne, Algebraic Geometry, II.2 and II.5;
Schoen, Compositio Mathematica 65 (1988), §2, printed p. 12. -/
theorem s2e_branchIdeal_section_parameter_divisibility
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (γ : g3_power Z (n + 1) ⟶ B) (a : ComplexPoint Z)
    (x : ComplexPoint (g3_power Z n)) (U : B.left.affineOpens)
    (hx : γ.left ((s2c_branchInsertion Z n a).left x.underlying) ∈ U.1)
    (s : Γ(B.left, U.1)) (hs : s ∈ (s2c_branchIdeal Z B n γ a).ideal U) :
    γ.left.stalkMap ((s2c_branchInsertion Z n a).left x.underlying)
      (B.left.presheaf.germ U.1 (γ.left ((s2c_branchInsertion Z n a).left x.underlying)) hx s) ∈
        Ideal.span (Set.singleton (s2e_curvePowerParameter Z (n + 1)
          (Point.map (s2c_branchInsertion Z n a) x) 0)) := by
  let f := s2c_branchInsertion Z n a ≫ γ
  have hz : (f.left.app U.1).hom s = 0 := f.left.ideal_ker_le U hs
  have hk : B.left.presheaf.germ U.1 (f.left x.underlying) hx s ∈
      RingHom.ker (f.left.stalkMap x.underlying).hom := by
    change f.left.stalkMap x.underlying
      (B.left.presheaf.germ U.1 (f.left x.underlying) hx s) = 0
    rw [f.left.germ_stalkMap_apply, hz, map_zero]
  rw [s2e_branch_composite_stalk_kernel] at hk
  exact hk

end HodgeLean.Foundations.Program
