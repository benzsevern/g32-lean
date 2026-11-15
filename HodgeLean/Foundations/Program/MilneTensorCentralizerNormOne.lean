import HodgeLean.Foundations.Program.MilneCentralizer
import HodgeLean.Foundations.Program.MilneFactors
import HodgeLean.Foundations.Program.MilneTensorDefs

noncomputable section
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program

theorem m1b_centralizer_norm_one_set (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (τ : (m0_endCentralizer J) ≃ₗ[ℂ] (m0_endCentralizer J))
    (hadj : ∀ (a : m0_endCentralizer J) (x y : ℂ ⊗[ℚ] HQ J 1),
      m0_form J pol hη ((a : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) x) y =
        m0_form J pol hη x ((τ a : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) y)) :
    g32p_lefschetz J pol =
      {u | ∃ a : m0_endCentralizer J,
        (a : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) = u ∧ τ a * a = 1} := by
  ext u
  rw [m0_mem_lefschetz_norm_one J pol hη u]
  constructor
  · rintro ⟨hu, v, hv, hvu⟩
    let a : m0_endCentralizer J := ⟨u, hu⟩
    have heq : v = (τ a : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) := by
      apply LinearMap.ext
      intro y
      apply sub_eq_zero.mp
      apply (m0_form_nondegenerate J pol hη).2
      intro x
      rw [map_sub]
      exact sub_eq_zero.mpr ((hv x y).symm.trans (hadj a x y))
    refine ⟨a, rfl, Subtype.ext ?_⟩
    change (τ a : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) * u = 1
    rw [← heq]
    exact hvu
  · rintro ⟨a, rfl, ha⟩
    refine ⟨a.property, (τ a : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)), hadj a, ?_⟩
    exact congrArg Subtype.val ha

end HodgeLean.Foundations.Program
