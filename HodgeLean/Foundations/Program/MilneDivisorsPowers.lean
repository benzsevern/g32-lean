import HodgeLean.Foundations.Program.MilneDivisorsDefs

noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

def m2_powerOneInv (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r : ℕ) :
    (ℂ ⊗[ℚ] HQ (g3_power J r) 1) →ₗ[ℂ] (Fin r → ℂ ⊗[ℚ] HQ J 1) :=
  LinearMap.pi fun i => (homPullback (g3_incl J r i) 1).baseChange ℂ

theorem m2_power_incl_proj (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r : ℕ) (i j : Fin r) :
    (homPullback (g3_incl J r i) 1).baseChange ℂ ∘ₗ
      (homPullback (g3_proj J r j) 1).baseChange ℂ =
      if i = j then LinearMap.id else 0 := by
  rw [← LinearMap.baseChange_comp, ← spec_homPullback_comp, spec_g3_incl_proj]
  split_ifs <;> simp only [spec_homPullback_id, spec_homPullback_one,
    LinearMap.baseChange_id, LinearMap.baseChange_zero]

theorem m2_powerOneInv_comp (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r : ℕ) :
    m2_powerOneInv J r ∘ₗ g32p_powerOne J r = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro v
  funext i
  change (homPullback (g3_incl J r i) 1).baseChange ℂ (g32p_powerOne J r v) = v i
  simp only [g32p_powerOne, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, map_sum]
  calc
    _ = ∑ j : Fin r, if i = j then v j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← LinearMap.comp_apply, m2_power_incl_proj]
      split_ifs <;> rfl
    _ = v i := by simp

theorem m2_power_sum_proj_incl (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r : ℕ) :
    (∑ i, homPullback (g3_proj J r i) 1 ∘ₗ homPullback (g3_incl J r i) 1) = LinearMap.id := by
  classical
  have hprod : homPullback (∏ i, g3_proj J r i ≫ g3_incl J r i) 1 =
      ∑ i, homPullback (g3_proj J r i ≫ g3_incl J r i) 1 := by
    induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, spec_homPullback_one]
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, spec_homPullback_mul, ih]
  calc
    _ = ∑ i, homPullback (g3_proj J r i ≫ g3_incl J r i) 1 := by
      apply Finset.sum_congr rfl
      intro i _
      exact (spec_homPullback_comp _ _ 1).symm
    _ = homPullback (∏ i, g3_proj J r i ≫ g3_incl J r i) 1 := hprod.symm
    _ = LinearMap.id := by rw [spec_g3_prod_proj_incl, spec_homPullback_id]

theorem m2_powerOne_compInv (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r : ℕ) :
    g32p_powerOne J r ∘ₗ m2_powerOneInv J r = LinearMap.id := by
  classical
  have h : (∑ i, (homPullback (g3_proj J r i) 1).baseChange ℂ ∘ₗ
      (homPullback (g3_incl J r i) 1).baseChange ℂ) = LinearMap.id := by
    calc
      _ = (∑ i, homPullback (g3_proj J r i) 1 ∘ₗ
          homPullback (g3_incl J r i) 1).baseChange ℂ := by
        simp only [← LinearMap.baseChange_comp]
        exact (map_sum (LinearMap.baseChangeHom ℚ ℂ _ _)
          (fun i : Fin r => homPullback (g3_proj J r i) 1 ∘ₗ
            homPullback (g3_incl J r i) 1) Finset.univ).symm
      _ = LinearMap.id := by rw [m2_power_sum_proj_incl, LinearMap.baseChange_id]
  apply LinearMap.ext
  intro z
  simpa only [g32p_powerOne, m2_powerOneInv, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.pi_apply, LinearMap.proj_apply, LinearMap.id_apply]
    using LinearMap.congr_fun h z

def m2_powerOneEquiv (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r : ℕ) :
    (Fin r → ℂ ⊗[ℚ] HQ J 1) ≃ₗ[ℂ] ℂ ⊗[ℚ] HQ (g3_power J r) 1 :=
  LinearEquiv.ofLinearMap (g32p_powerOne J r) (m2_powerOneInv J r)
    (m2_powerOne_compInv J r) (m2_powerOneInv_comp J r)

theorem m2_powerOne_bijective (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r : ℕ) :
    Function.Bijective (g32p_powerOne J r) := (m2_powerOneEquiv J r).bijective

theorem m2_powerClass_bijective (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r n : ℕ) :
    Function.Bijective (g32p_powerClass J r n) := by
  let hT := torusCohomology_cupProductOf (g3_power J r)
  letI := hT.finite
  have h1 := m2_powerOne_bijective J r
  have he : Function.Bijective (exteriorPower.map n (g32p_powerOne J r)) :=
    ⟨exteriorPower.map_injective_field h1.1, exteriorPower.map_surjective h1.2⟩
  exact ((hT.cupWedgeEquiv n).baseChange ℚ ℂ _ _).bijective.comp
    ((HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv n).symm.bijective.comp he)

end HodgeLean.Foundations.Program
