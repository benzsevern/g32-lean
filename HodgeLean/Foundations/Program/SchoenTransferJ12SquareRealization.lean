import HodgeLean.Foundations.Program.SchoenTransferJ12HodgeReflection
import HodgeLean.Foundations.Program.UniversalFamilyB60cHom

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- Realize the rational upper map of an injective abelian square on the specified source. -/
theorem s4_selected_square_realization
    (B D P : Over (Spec ↧ℂ)) [GrpObj B] [GrpObj D] [GrpObj P]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    [IsIntegral D.left] [Smooth D.hom] [IsProjective D.hom]
    [IsIntegral P.left] [Smooth P.hom] [IsProjective P.hom]
    (f : D ⟶ B) [IsMonHom f] (g : D ⟶ P) [IsMonHom g]
    (hf : Function.Injective (homPullback f 1))
    (T : HQ P 1 →ₗ[ℚ] HQ B 1)
    (hsq : (homPullback f 1).comp T = homPullback g 1)
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (j : X ⟶ B) :
    ∃ (N : ℕ) (u : X ⟶ P), 0 < N ∧
      ∀ v, homPullback u 1 v = (N : ℚ) • homPullback j 1 (T v) := by
  have hT := s4_selected_abelian_square_holomorphic B D P f g hf T hsq
  obtain ⟨N, hN, u, _, hu⟩ := b60c_hom_of_holomorphic B P T hT
  refine ⟨N, j ≫ u, hN, ?_⟩
  intro v
  rw [spec_homPullback_comp, hu, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]

#print axioms s4_selected_square_realization

end HodgeLean.Foundations.Program
