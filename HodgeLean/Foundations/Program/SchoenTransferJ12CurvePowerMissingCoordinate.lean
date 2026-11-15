import HodgeLean.Foundations.Program.SchoenTransferJ12CurveConstant

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters
open scoped TensorProduct BigOperators
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- A degree-one cup missing a curve coordinate has zero all-degree-one extraction. -/
theorem s4_selected_curve_power_extract_missing_coordinate
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (n : ℕ)
    [IsIntegral (g3_power Y n).left] [Smooth (g3_power Y n).hom]
    [IsProjective (g3_power Y n).hom]
    (a : Fin n → Fin n) (ha : ¬ Function.Surjective a) (v : Fin n → HQ Y 1) :
    s4_selected_curve_power_extract Y hdim n
      ((cupProductOf (g3_power Y n)).cupMulti n
        (fun i => homPullback (g3_proj Y n (a i)) 1 (v i))) = 0 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, ∀ i, a i ≠ j := by
    simpa only [Function.Surjective, not_forall, not_exists] using ha
  letI := connectedSpace_complexPoint Y
  let p : ComplexPoint Y := Classical.choice inferInstance
  let c : Y ⟶ Y := (Over.homMk Y.hom : Y ⟶ Over.mk (𝟙 (Spec ↧ℂ))) ≫ p
  let b : Fin n → (Y ⟶ Y) := fun i => if i = j then c else 𝟙 Y
  let u : g3_power Y n ⟶ g3_power Y n :=
    s2_lift n (fun i => g3_proj Y n i ≫ b i)
  have hu (i : Fin n) : u ≫ g3_proj Y n i = g3_proj Y n i ≫ b i :=
    s4_e1_lift_proj n _ i
  have hb : ∃ i, homPullback (b i) 1 = 0 := by
    refine ⟨j, ?_⟩
    simp only [b, if_pos rfl]
    exact s4_selected_curve_constant_pullback Y p
  have hfix (i : Fin n) :
      homPullback u 1 (homPullback (g3_proj Y n (a i)) 1 (v i)) =
        homPullback (g3_proj Y n (a i)) 1 (v i) := by
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, hu]
    simp only [b, if_neg (hj i), Category.comp_id]
  let x := (cupProductOf (g3_power Y n)).cupMulti n
    (fun i => homPullback (g3_proj Y n (a i)) 1 (v i))
  have hux : homPullback u n x = x := by
    dsimp only [x]
    rw [s4_e1_cupMulti_pullback]
    simp only [hfix]
  have hz := LinearMap.congr_fun
    (s4_selected_curve_power_extract_coordinate_zero Y hdim n u b hu hb) x
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply, hux] using hz

#print axioms s4_selected_curve_power_extract_missing_coordinate
end HodgeLean.Foundations.Program
