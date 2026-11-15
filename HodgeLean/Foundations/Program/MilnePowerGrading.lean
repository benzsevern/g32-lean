import HodgeLean.Foundations.Program.MilneDivisorsGroup
import HodgeLean.Foundations.Program.MilneDivisorsPowers

noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

def m2_hodgeGrading (J : Over (Spec ↧ℂ)) [GrpObj J] [IsIntegral J.left]
    [Smooth J.hom] [IsProjective J.hom] : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1) :=
  let M := cohomologyHodgeStructure (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
    (hodgeDecomposition_of_abelian J) 1
  gradingOperator M.H M.isInternal

theorem m2_hodgeGrading_pullback {X Y : Over (Spec ↧ℂ)} [GrpObj X] [GrpObj Y]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ X) [IsMonHom f] :
    (homPullback f 1).baseChange ℂ ∘ₗ m2_hodgeGrading X =
      m2_hodgeGrading Y ∘ₗ (homPullback f 1).baseChange ℂ := by
  let MX := cohomologyHodgeStructure (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
    (hodgeDecomposition_of_abelian X) 1
  let MY := cohomologyHodgeStructure (finiteBetti_abelian Y) (spec_bettiDeRhamIso_abelian Y)
    (hodgeDecomposition_of_abelian Y) 1
  refine linearMap_ext_of_isInternal MX.isInternal fun pq x hx => ?_
  have hfx : (homPullback f 1).baseChange ℂ x ∈ MY.H pq :=
    spec_homPullback_hodgePiece_one f pq (Submodule.mem_map_of_mem hx)
  change (homPullback f 1).baseChange ℂ (gradingOperator MX.H MX.isInternal x) =
    gradingOperator MY.H MY.isInternal ((homPullback f 1).baseChange ℂ x)
  rw [gradingOperator_apply_of_mem MX.H MX.isInternal hx,
    gradingOperator_apply_of_mem MY.H MY.isInternal hfx, map_smul]

theorem m2_hodgeGrading_square (J : Over (Spec ↧ℂ)) [GrpObj J] [IsIntegral J.left]
    [Smooth J.hom] [IsProjective J.hom] (x : ℂ ⊗[ℚ] HQ J 1) :
    m2_hodgeGrading J (m2_hodgeGrading J x) = -x := by
  let M := cohomologyHodgeStructure (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
    (hodgeDecomposition_of_abelian J) 1
  have hsupp : ∀ pq : ℤ × ℤ, pq ≠ (1, 0) → pq ≠ (0, 1) → M.H pq = ⊥ := by
    intro pq h10 h01
    exact cohomologyHodgePiece_one_eq_bot J pq h10 h01
  exact LinearMap.congr_fun
    (spec_eqw_gradingOperator_mul_self (H := M.H) (hH := M.isInternal) hsupp) x


theorem m2_powerOne_grading (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r : ℕ) :
    g32p_powerOne J r ∘ₗ g32p_diag J (m2_hodgeGrading J) r =
      m2_hodgeGrading (g3_power J r) ∘ₗ g32p_powerOne J r := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, g32p_powerOne, LinearMap.sum_apply,
    LinearMap.proj_apply, g32p_diag, LinearMap.pi_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  letI : IsMonHom (g3_proj J r i) := spec_g3_isMonHom_proj J r i
  exact LinearMap.congr_fun (m2_hodgeGrading_pullback (g3_proj J r i)) (v i)


end HodgeLean.Foundations.Program
