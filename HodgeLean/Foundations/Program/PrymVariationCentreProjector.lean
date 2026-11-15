import HodgeLean.Foundations.Program.PrymVariationCentreRepresentation

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem b63d_naturalRep_apply (g : b4b_Group) :
    b63d_naturalRep g = Matrix.toLin' (b4b_toMatrix g) := rfl

theorem b63d_naturalRep_projector :
    (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • b63d_naturalRep g) =
      (b4b_projectorDenominator : ℂ) •
        Matrix.toLin' (Matrix.single 0 0 1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ Matrix.toLin' M)
    b63l_projector_matrix
  simpa only [map_sum, map_smul, b63d_naturalRep_apply] using h

theorem b63d_naturalRep_projector_apply (v : Fin 4 → ℂ) :
    (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • b63d_naturalRep g) v =
      ((b4b_projectorDenominator : ℂ) * v 0) • Pi.single 0 1 := by
  rw [b63d_naturalRep_projector]
  simp only [LinearMap.smul_apply, Matrix.toLin'_apply, Matrix.single_mulVec_eq,
    one_mul, smul_smul]

theorem b63d_naturalRep_projector_range :
    LinearMap.range (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • b63d_naturalRep g) =
      Submodule.span ℂ {(Pi.single 0 1 : Fin 4 → ℂ)} := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [b63d_naturalRep_projector_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    rintro v rfl
    refine ⟨(b4b_projectorDenominator : ℂ)⁻¹ • Pi.single 0 1, ?_⟩
    rw [b63d_naturalRep_projector_apply]
    norm_num [b4b_projectorDenominator]

theorem b63d_naturalRep_projector_rank :
    Module.finrank ℂ (LinearMap.range
      (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • b63d_naturalRep g)) = 1 := by
  rw [b63d_naturalRep_projector_range]
  apply finrank_span_singleton
  intro h
  have hz := congrFun h 0
  norm_num at hz

end HodgeLean.Foundations.Program
