import HodgeLean.Foundations.Program.G32SelectedRealizationIntegral

noncomputable section
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open scoped TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program

theorem g32y_homPullback_prod {H : Type*} [Fintype H]
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (f : H → (X ⟶ X)) (z : H → ℤ) :
    homPullback (∏ h, f h ^ z h) 1 = ∑ h, (z h : ℚ) • homPullback (f h) 1 := by
  classical
  have hs (s : Finset H) : homPullback (∏ h ∈ s, f h ^ z h) 1 =
      ∑ h ∈ s, (z h : ℚ) • homPullback (f h) 1 := by
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, spec_homPullback_one]
    | @insert h s hh ih =>
      rw [Finset.prod_insert hh, Finset.sum_insert hh, spec_homPullback_mul,
        spec_homPullback_zpow, ih]
  exact hs Finset.univ

theorem g32y_integral_projector {H : Type*} [Fintype H]
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (f : H → AbelianEnd X) (u : H → ℚ)
    (he : (∑ h, u h • abelianEndAction X (f h)) ∘ₗ
        (∑ h, u h • abelianEndAction X (f h)) = ∑ h, u h • abelianEndAction X (f h)) :
    ∃ N : ℕ, 0 < N ∧ ∃ F : AbelianEnd X,
      abelianEndAction X F = (N : ℚ) • ∑ h, u h • abelianEndAction X (f h) ∧
      abelianEndAction X F ∘ₗ abelianEndAction X F = (N : ℚ) • abelianEndAction X F := by
  classical
  obtain ⟨N, hN, z, hz⟩ := g32y_clear_denominators u
  let A : AbelianEnd X →+ Module.End ℚ (HQ X 1) := {
    toFun := abelianEndAction X
    map_zero' := spec_abelianEndAction_zero X
    map_add' := spec_abelianEndAction_add X }
  let F : AbelianEnd X := ∑ h, z h • f h
  have hF : abelianEndAction X F = (N : ℚ) • ∑ h, u h • abelianEndAction X (f h) := by
    change A (∑ h, z h • f h) = _
    rw [map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [map_zsmul, smul_smul, hz, Int.cast_smul_eq_zsmul]
    rfl
  refine ⟨N, hN, F, hF, ?_⟩
  rw [hF, LinearMap.smul_comp, LinearMap.comp_smul, he]

theorem g32y_abelianEnd_sum_hom {H : Type*} [Fintype H]
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
    (f : H → AbelianEnd X) (z : H → ℤ) :
    (∑ h, z h • f h).hom = ∏ h, (f h).hom ^ z h := by
  classical
  let B : AbelianEnd X →+ Additive (X ⟶ X) := {
    toFun := fun f ↦ Additive.ofMul f.hom
    map_zero' := rfl
    map_add' := fun _ _ ↦ rfl }
  change Additive.toMul (B (∑ h, z h • f h)) = _
  rw [map_sum, toMul_sum]
  apply Finset.prod_congr rfl
  intro h _
  rw [map_zsmul, toMul_zsmul]
  rfl

end HodgeLean.Foundations.Program
