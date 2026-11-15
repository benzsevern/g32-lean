import HodgeLean.Foundations.Program.CompensationAssemblyDefs

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

theorem cq_degree_one_product_equiv (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] :
    ∃ e : (HQ A 1 × HQ Y 1) ≃ₗ[ℚ] HQ (A ⊗ Y) 1,
      (∀ a, e (a, 0) = homPullback (fst A Y) 1 a) ∧
      (∀ b, e (0, b) = homPullback (snd A Y) 1 b) := by
  let i : A ⟶ A ⊗ Y := lift (𝟙 A) 1
  let j : Y ⟶ A ⊗ Y := lift 1 (𝟙 Y)
  have hip : i ≫ fst A Y = 𝟙 A := lift_fst _ _
  have hiq : i ≫ snd A Y = 1 := lift_snd _ _
  have hjp : j ≫ fst A Y = 1 := lift_fst _ _
  have hjq : j ≫ snd A Y = 𝟙 Y := lift_snd _ _
  have hsum : (fst A Y ≫ i) * (snd A Y ≫ j) = 𝟙 (A ⊗ Y) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [MonObj.mul_comp, Category.assoc, Category.assoc, hip, hjp,
        Category.comp_id, MonObj.comp_one, mul_one, Category.id_comp]
    · rw [MonObj.mul_comp, Category.assoc, Category.assoc, hiq, hjq,
        MonObj.comp_one, Category.comp_id, one_mul, Category.id_comp]
  let F := LinearMap.coprod (homPullback (fst A Y) 1) (homPullback (snd A Y) 1)
  let G := LinearMap.prod (homPullback i 1) (homPullback j 1)
  have hGF : G ∘ₗ F = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    apply Prod.ext
    · change homPullback i 1 (homPullback (fst A Y) 1 a + homPullback (snd A Y) 1 b) = a
      rw [map_add, ← LinearMap.comp_apply, ← spec_homPullback_comp, hip,
        spec_homPullback_id, LinearMap.id_apply,
        ← LinearMap.comp_apply, ← spec_homPullback_comp, hiq,
        spec_homPullback_one, LinearMap.zero_apply, add_zero]
    · change homPullback j 1 (homPullback (fst A Y) 1 a + homPullback (snd A Y) 1 b) = b
      rw [map_add, ← LinearMap.comp_apply, ← spec_homPullback_comp, hjp,
        spec_homPullback_one, LinearMap.zero_apply,
        ← LinearMap.comp_apply, ← spec_homPullback_comp, hjq,
        spec_homPullback_id, LinearMap.id_apply, zero_add]
  have hFG : F ∘ₗ G = LinearMap.id := by
    have h := congrArg (fun f => homPullback f 1) hsum
    rw [spec_homPullback_mul, spec_homPullback_comp, spec_homPullback_comp,
      spec_homPullback_id] at h
    exact h
  let e : (HQ A 1 × HQ Y 1) ≃ₗ[ℚ] HQ (A ⊗ Y) 1 := LinearEquiv.ofLinear F G hFG hGF
  refine ⟨e, ?_, ?_⟩
  · intro a
    change homPullback (fst A Y) 1 a + homPullback (snd A Y) 1 0 = _
    rw [map_zero, add_zero]
  · intro b
    change homPullback (fst A Y) 1 0 + homPullback (snd A Y) 1 b = _
    rw [map_zero, zero_add]

end HodgeLean.Foundations.Program
