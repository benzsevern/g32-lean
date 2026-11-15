import HodgeLean.Foundations.Program.PrymVariationCentreCommutant

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem b63d_naturalRep_commutant (P : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ))
    (hc : ∀ g v, P (b63d_naturalRep g v) = b63d_naturalRep g (P v)) :
    ∃ c : ℂ, P = c • LinearMap.id := by
  have hm (g : b4b_Group) :
      LinearMap.toMatrix' P * b4b_toMatrix g =
        b4b_toMatrix g * LinearMap.toMatrix' P := by
    have he : P.comp (b63d_naturalRep g) = (b63d_naturalRep g).comp P := by
      apply LinearMap.ext
      intro v
      exact hc g v
    have ht := congrArg LinearMap.toMatrix' he
    change LinearMap.toMatrix' (P.comp (Matrix.toLin' (b4b_toMatrix g))) =
      LinearMap.toMatrix' ((Matrix.toLin' (b4b_toMatrix g)).comp P) at ht
    simpa only [LinearMap.toMatrix'_comp,
      LinearMap.toMatrix'_toLin'] using ht
  have hp := b63d_matrix_commutant (LinearMap.toMatrix' P)
    (hm (b4b_generators 0)) (hm (b4b_generators 1)) (hm (b4b_generators 2))
  refine ⟨LinearMap.toMatrix' P 0 0, ?_⟩
  apply LinearMap.toMatrix'.injective
  simpa only [map_smul, LinearMap.toMatrix'_id] using hp

instance b63d_naturalRep_isIrreducible : b63d_naturalRep.IsIrreducible where
  exists_pair_ne := ⟨⊥, ⊤, by
    intro h
    have hv : (fun _ : Fin 4 ↦ (1 : ℂ)) ∈
        (⊥ : Subrepresentation b63d_naturalRep).toSubmodule := by
      rw [h]
      trivial
    have hz := congrFun ((Submodule.mem_bot ℂ).mp hv) 0
    norm_num at hz⟩
  eq_bot_or_eq_top S := by
    obtain ⟨P, hPU, hPid, hPσ⟩ := b4cov_exists_equivariantProj b63d_naturalRep
      S.toSubmodule (fun g v hv ↦ S.apply_mem_toSubmodule g hv)
    obtain ⟨c, hP⟩ := b63d_naturalRep_commutant P hPσ
    by_cases hc : c = 0
    · left
      apply Subrepresentation.toSubmodule_injective
      apply eq_bot_iff.mpr
      intro v hv
      have he := hPid v hv
      rw [hP, hc, zero_smul, LinearMap.zero_apply] at he
      exact (Submodule.mem_bot ℂ).mpr he.symm
    · right
      apply Subrepresentation.toSubmodule_injective
      apply top_unique
      intro v hv
      have he := S.toSubmodule.smul_mem c⁻¹ (hPU v)
      rw [hP, LinearMap.smul_apply, LinearMap.id_apply, inv_smul_smul₀ hc] at he
      exact he

example : (HurwitzPrymRex_barRep b63d_naturalRep).IsIrreducible := inferInstance

end HodgeLean.Foundations.Program
