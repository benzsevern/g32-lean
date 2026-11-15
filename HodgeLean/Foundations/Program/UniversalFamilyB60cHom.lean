import HodgeLean.Adapters.GagaWiring
import HodgeLean.Adapters.AbelianHomPullbackDegrees

noncomputable section
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Apply the endomorphism realization theorem to the off-diagonal block on a product,
then compose with the inclusion and projection of its factors. -/
theorem b60c_hom_of_holomorphic
    (X Y : Over (Spec ↧ℂ)) [GrpObj X] [GrpObj Y]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (T : HQ Y 1 →ₗ[ℚ] HQ X 1)
    (hT : (complexHolomorphicH1 Y).map (T.baseChange ℂ) ≤ complexHolomorphicH1 X) :
    ∃ N : ℕ, 0 < N ∧ ∃ f : X ⟶ Y,
      IsMonHom f ∧ homPullback f 1 = (N : ℚ) • T := by
  let Z := X ⊗ Y
  letI : IsIntegral Z.left := gagam_product_isIntegral X Y
  letI : Smooth Z.hom := gagam_product_smooth X Y
  letI : IsProjective Z.hom := gagam_product_projective X Y
  letI : GrpObj Z := GrpObj.tensorObj.instTensorObj
  haveI : IsCommMonObj Z :=
    HodgeLean.Foundations.isCommMonObj_of_complexSelfProductIntegral Z
      (HodgeLean.Foundations.complexSelfProductIntegral_of_isIntegral Z)
  let iX : X ⟶ Z := lift (𝟙 X) 1
  let iY : Y ⟶ Z := lift 1 (𝟙 Y)
  haveI : IsMonHom (1 : X ⟶ Y) := by rw [Hom.one_def]; infer_instance
  haveI : IsMonHom (1 : Y ⟶ X) := by rw [Hom.one_def]; infer_instance
  haveI : IsMonHom iX := inferInstanceAs (IsMonHom (lift (𝟙 X) (1 : X ⟶ Y)))
  haveI : IsMonHom iY := inferInstanceAs (IsMonHom (lift (1 : Y ⟶ X) (𝟙 Y)))
  let U : Module.End ℚ (HQ Z 1) := homPullback (fst X Y) 1 ∘ₗ T ∘ₗ homPullback iY 1
  have hU : (complexHolomorphicH1 Z).map (U.baseChange ℂ) ≤ complexHolomorphicH1 Z := by
    rintro _ ⟨v, hv, rfl⟩
    dsimp only [U]
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp]
    exact (spec_homPullback_hodge (fst X Y)).1 (Submodule.mem_map_of_mem
      (hT (Submodule.mem_map_of_mem
        ((spec_homPullback_hodge iY).1 (Submodule.mem_map_of_mem hv)))))
  obtain ⟨N, hN, g, hg⟩ := gagaw_spec_exists_abelianEnd_of_hodge Z U hU
  refine ⟨N, hN, iX ≫ g.hom ≫ snd X Y, inferInstance, ?_⟩
  have hg' : homPullback g.hom 1 = (N : ℚ) • U := hg
  rw [spec_homPullback_comp, spec_homPullback_comp, hg']
  ext v
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, U]
  have hY : homPullback iY 1 (homPullback (snd X Y) 1 v) = v := by
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp]
    simp only [iY, lift_snd, spec_homPullback_id, LinearMap.id_apply]
  rw [hY]
  congr 1
  rw [← LinearMap.comp_apply, ← spec_homPullback_comp]
  simp only [iX, lift_fst, spec_homPullback_id, LinearMap.id_apply]

#print axioms b60c_hom_of_holomorphic

end HodgeLean.Foundations.Program
