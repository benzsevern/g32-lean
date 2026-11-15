import HodgeLean.Foundations.Program.SchoenBaseChangedProducts
import HodgeLean.Foundations.Program.SchoenCoordinateActionLaws
import HodgeLean.Foundations.Program.SchoenSegrePowerEquivariance

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- The actual retained complex projective-space power is the base change of its integral finite-product model. -/
def s2_segrePowerComplexIso (d n : ℕ) :
    g3_power ((s2_terminalBaseChange (Spec ↧ℂ)).obj (g3c_P d)) n ≅
      (s2_terminalBaseChange (Spec ↧ℂ)).obj (s2_segrePower d n) := by
  let S := Spec ↧ℂ
  let F := s2_terminalBaseChange S
  let P := F.obj (g3c_P d)
  refine ⟨s2_baseChangedProductLift S n (fun _ => g3c_P d) (fun i => g3_proj P n i),
    s2_lift n (fun i => F.map (s2_schemeProductπ n (fun _ => g3c_P d) i)), ?_, ?_⟩
  · apply s2_product_hom_ext n
    intro i
    rw [Category.assoc, s2_check_lift_proj, Category.id_comp]
    exact s2_baseChangedProductLift_π S n (fun _ => g3c_P d) _ i
  · apply s2_baseChangedProduct_hom_ext S n (fun _ => g3c_P d)
    intro i
    rw [Category.assoc, s2_baseChangedProductLift_π, s2_check_lift_proj, Category.id_comp]

/-- The actual complex power comparison preserves each retained projective coordinate projection. -/
theorem s2_segrePowerComplexIso_hom_π (d n : ℕ) (i : Fin n) :
    (s2_segrePowerComplexIso d n).hom ≫ (s2_terminalBaseChange (Spec ↧ℂ)).map
      (s2_schemeProductπ n (fun _ => g3c_P d) i) =
        g3_proj ((s2_terminalBaseChange (Spec ↧ℂ)).obj (g3c_P d)) n i :=
  s2_baseChangedProductLift_π (Spec ↧ℂ) n (fun _ => g3c_P d) _ i

/-- The actual complex power comparison intertwines retained coordinate permutations with base change of integral factor permutations. -/
theorem s2_segrePowerComplexIso_permute (d n : ℕ) (σ : Equiv.Perm (Fin n)) :
    s2_permute ((s2_terminalBaseChange (Spec ↧ℂ)).obj (g3c_P d)) n σ ≫
        (s2_segrePowerComplexIso d n).hom =
      (s2_segrePowerComplexIso d n).hom ≫
        (s2_terminalBaseChange (Spec ↧ℂ)).map (s2_segrePowerPerm d n σ) := by
  apply s2_baseChangedProduct_hom_ext (Spec ↧ℂ) n (fun _ => g3c_P d)
  intro i
  simp only [Category.assoc, s2_segrePowerComplexIso_hom_π]
  rw [← Functor.map_comp, s2_segrePowerPerm_π, s2_segrePowerComplexIso_hom_π]
  simp only [s2_permute, s2_check_lift_proj]

end HodgeLean.Foundations.Program
