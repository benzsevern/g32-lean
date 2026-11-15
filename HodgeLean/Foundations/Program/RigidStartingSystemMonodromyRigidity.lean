import HodgeLean.Foundations.Program.RigidStartingSystemPrintedGroup
import HodgeLean.Foundations.Program.RigidStartingSystemRigidity
import HodgeLean.Foundations.Program.RigidStartingSystemFourPointCentralizers
import HodgeLean.Foundations.Program.RigidStartingSystemIrreducibility

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b65r_rigid_monodromy_factorization {Γ : Type} [Group Γ]
    (γ : Fin 4 → Γ) (hγ : (List.ofFn γ).prod = 1)
    (hu : ∀ (G : Type) [Group G] (v : Fin 4 → G), (List.ofFn v).prod = 1 →
      ∃! φ : Γ →* G, ∀ i, φ (γ i) = v i)
    (M : Γ →* ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hloc : ∀ i, ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
      C*b65r_printedOperatorHom (b4b_generators i)*C⁻¹ = M (γ i)) :
    ∃ ρ : Γ →* b4b_Group, Function.Surjective ρ ∧
      ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
        ∀ g, (M g).val = C.val*b65r_operator (b4b_toMatrix (ρ g))*(C⁻¹).val := by
  let T := fun i ↦ b65r_printedUnitHom (b4b_generators i)
  let S := fun i ↦ b65r_operatorUnitsEquiv.symm (M (γ i))
  have hT : (List.ofFn T).prod = 1 := by
    rw [show List.ofFn T = (List.ofFn b4b_generators).map b65r_printedUnitHom by
      rw [List.map_ofFn]; rfl,← map_list_prod,b65r_printed_generators_prod,map_one]
  have hS : (List.ofFn S).prod = 1 := by
    rw [show List.ofFn S = (List.ofFn γ).map (b65r_operatorUnitsEquiv.symm.toMonoidHom.comp M) by
      rw [List.map_ofFn]; rfl,← map_list_prod,hγ,map_one]
  have hL : ∀ i, ∃ C : (Matrix (Fin 4) (Fin 4) ℂ)ˣ, C*T i*C⁻¹ = S i := by
    intro i
    obtain ⟨C,hC⟩ := hloc i
    refine ⟨b65r_operatorUnitsEquiv.symm C,?_⟩
    have hh := congrArg b65r_operatorUnitsEquiv.symm hC
    simpa only [map_mul,map_inv,b65r_printedOperatorHom,MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply] using hh
  obtain ⟨D,hD⟩ := b65r_simultaneous_conjugacy T S hT hS
    b65r_four_point_irreducible b65r_printed_index hL
  let C := b65r_operatorUnitsEquiv D
  have hC (i : Fin 4) : C*b65r_printedOperatorHom (b4b_generators i)*C⁻¹ = M (γ i) := by
    have hh := congrArg b65r_operatorUnitsEquiv (hD i)
    simpa [T,S,C,b65r_printedOperatorHom] using hh
  obtain ⟨ρ,hρ,-⟩ := hu b4b_Group b4b_generators b65r_printed_generators_prod
  let N : Γ →* ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ :=
    (MulAut.conj C).toMonoidHom.comp (b65r_printedOperatorHom.comp ρ)
  have hN : ∀ i, N (γ i) = M (γ i) := by
    intro i
    simpa only [N,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,hρ] using hC i
  obtain ⟨φ,hφ,huniq⟩ := hu _ (fun i ↦ M (γ i)) (by
    have hp := congrArg M hγ
    simpa only [map_list_prod,List.map_ofFn,Function.comp_def,map_one] using hp)
  have heq : M = N := (huniq M (fun _ ↦ rfl)).trans (huniq N hN).symm
  refine ⟨ρ,b65r_printed_generators_surjective ρ γ hρ,C,fun g ↦ ?_⟩
  rw [heq]
  change (C*b65r_printedOperatorHom (ρ g)*C⁻¹).val = _
  simp only [Units.val_mul,b65r_printedOperatorHom_val]

end HodgeLean.Foundations.Program
