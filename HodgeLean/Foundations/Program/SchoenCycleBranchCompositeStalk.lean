import HodgeLean.Foundations.Program.SchoenCycleInsertionStalkKernel

/-! # Exact stalk kernels in the actual marked branch composite -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual branch composite's stalk kernel is the contraction of the
marked regular parameter ideal along the retained quotient stalk map.
Source: Hartshorne, Algebraic Geometry, II.2;
Schoen, Compositio Mathematica 65 (1988), §2, printed p. 12. -/
theorem s2e_branch_composite_stalk_kernel
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (γ : g3_power Z (n + 1) ⟶ B) (a : ComplexPoint Z)
    (x : ComplexPoint (g3_power Z n)) :
    RingHom.ker ((s2c_branchInsertion Z n a ≫ γ).left.stalkMap x.underlying).hom =
      Ideal.comap (γ.left.stalkMap ((s2c_branchInsertion Z n a).left x.underlying)).hom
        (Ideal.span (Set.singleton (s2e_curvePowerParameter Z (n + 1)
          (Point.map (s2c_branchInsertion Z n a) x) 0))) := by
  change RingHom.ker (((s2c_branchInsertion Z n a).left ≫ γ.left).stalkMap x.underlying).hom = _
  rw [Scheme.Hom.stalkMap_comp]
  change RingHom.ker (((s2c_branchInsertion Z n a).left.stalkMap x.underlying).hom.comp
    (γ.left.stalkMap ((s2c_branchInsertion Z n a).left x.underlying)).hom) = _
  rw [← RingHom.comap_ker, s2e_branchInsertion_stalk_kernel]

end HodgeLean.Foundations.Program
