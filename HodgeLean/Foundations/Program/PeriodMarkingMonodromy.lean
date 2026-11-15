import HodgeLean.Foundations.Program.PeriodMarkingDefs
import HodgeLean.Foundations.Program.PrymVariationCentreChevalleyWeil

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b64b_peripheral_generates (Γ : Type) [Group Γ] (γ : Fin 13 → Γ)
    (hprod : (List.ofFn γ).reverse.prod = 1)
    (hgen : ∀ (H : Type) [Group H] (k : Fin 13 → H),
      (List.ofFn k).reverse.prod = 1 → ∃! ψ : Γ →* H, ∀ i, ψ (γ i) = k i) :
    Subgroup.closure (Set.range γ) = ⊤ := by
  let S := Subgroup.closure (Set.range γ)
  let k : Fin 13 → S := fun i => ⟨γ i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hk : (List.ofFn k).reverse.prod = 1 := by
    apply S.subtype_injective
    simpa only [map_list_prod, List.map_reverse, List.map_ofFn, map_one, Function.comp_def, k, Subgroup.subtype_apply] using hprod
  obtain ⟨ψ, hψ, _⟩ := hgen S k hk
  obtain ⟨ρ, _, hρ⟩ := hgen Γ γ hprod
  have he : S.subtype.comp ψ = MonoidHom.id Γ :=
    (hρ _ (fun i => congrArg Subtype.val (hψ i))).trans (hρ _ (fun _ => rfl)).symm
  apply top_unique
  intro x _
  have hx : (ψ x).val = x := DFunLike.congr_fun he x
  exact hx ▸ (ψ x).property

theorem b64b_root_monodromy_surjective (Γ : Type) [Group Γ]
    (γ : Fin 13 → Γ) (φ : Γ →* b4b_Groupᵐᵒᵖ)
    (hroot : ∀ i, φ (γ i) = MulOpposite.op (b4b_root i)) :
    Function.Surjective φ := by
  have hr : Subgroup.closure (Set.range b4b_root) ≤ φ.range.unop := by
    apply (Subgroup.closure_le _).2
    rintro _ ⟨i, rfl⟩
    exact ⟨γ i, hroot i⟩
  have ht : φ.range.unop = ⊤ := top_unique (b63d_root_subgroup ▸ hr)
  intro g
  have hg : MulOpposite.unop g ∈ φ.range.unop := by rw [ht]; trivial
  exact hg

end HodgeLean.Foundations.Program
