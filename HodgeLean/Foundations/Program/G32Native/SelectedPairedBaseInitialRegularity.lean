import HodgeLean.Foundations.Curves.SymmetricCharts.StageThree.Basic

/-! Stage-zero regularity with the retained selected branch representatives. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Apply the symmetric-curve intersection calculation without changing branch witnesses. -/
theorem g32l4_selected_initial_regularity
    (Y Z B₀ : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdim : TopologicalSpace.dim Z.left = 1) (h r : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B₀)
    (hinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) → ∃! d : B₀ ⟶ T, γ ≫ d = f)
    (p₀ : Y ⟶ Z) (C : Type*) (eY : C → ComplexPoint Y)
    {n : ℕ} (y : Fin n → C) (σ : Fin (2 * r) ≃ Fin n)
    (hy : Function.Injective (fun t => Point.map p₀ (eY (y t)))) :
    Smooth B₀.hom ∧ IsProjective B₀.hom ∧ IsIntegral B₀.left ∧
      ∀ J : Finset (Fin (2 * r)),
        let I := J.sup (fun t => s2c_branchIdeal Z B₀ h γ
          (Point.map p₀ (eY (y (σ t)))))
        Smooth (s2c_subscheme B₀ I).hom ∧
        (∀ x : (s2c_subscheme B₀ I).left,
          ∃ U : (s2c_subscheme B₀ I).left.Opens, x ∈ U ∧
            Nonempty (Scheme.Modules.restrict
              (s2c_conormal (s2c_subschemeι B₀ I).left) U.ι ≅
              (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin J.card) :
                U.toScheme.Modules))) ∧
        (h + 1 < J.card → IsEmpty (s2c_subscheme B₀ I).left) := by
  exact HodgeLean.Foundations.Curves.SymmetricCharts.StageThree.stage_zero_assembly
    Z hdim h r B₀ γ hinv huniv
    (fun t => Point.map p₀ (eY (y (σ t)))) (hy.comp σ.injective)

#print axioms g32l4_selected_initial_regularity
end HodgeLean.Foundations.Program
