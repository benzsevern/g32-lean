import HodgeLean.Foundations.Program.PrymVariationCentreProjector

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem b63d_conjugateRep_projector_val (v : HurwitzPrymRex_Bar (Fin 4 → ℂ)) :
    ((∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) •
      HurwitzPrymRex_barRep b63d_naturalRep g) v).val =
      (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • b63d_naturalRep g) v.val := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  change HurwitzPrymRex_Bar.addEquiv (∑ g : b4b_Group,
    (b4b_projectorCoeff g : ℂ) • HurwitzPrymRex_barRep b63d_naturalRep g v) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  change star (b4b_projectorCoeff g : ℂ) • b63d_naturalRep g v.val = _
  simp only [star_intCast]

theorem b63d_conjugateRep_projector_rank :
    Module.finrank ℂ (LinearMap.range (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) •
      HurwitzPrymRex_barRep b63d_naturalRep g)) = 1 := by
  let A := ∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • b63d_naturalRep g
  let B := ∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) •
    HurwitzPrymRex_barRep b63d_naturalRep g
  have hv (v : HurwitzPrymRex_Bar (Fin 4 → ℂ)) : (B v).val = A v.val :=
    b63d_conjugateRep_projector_val v
  let j : LinearMap.range B ≃+ LinearMap.range A :=
    { toFun := fun x ↦ ⟨x.val.val, by
        obtain ⟨v, h⟩ := x.property
        exact ⟨v.val, (hv v).symm.trans (congrArg HurwitzPrymRex_Bar.val h)⟩⟩
      invFun := fun x ↦ ⟨HurwitzPrymRex_Bar.of x.val, by
        obtain ⟨v, h⟩ := x.property
        refine ⟨HurwitzPrymRex_Bar.of v, ?_⟩
        apply HurwitzPrymRex_Bar.ext
        exact (hv (HurwitzPrymRex_Bar.of v)).trans h⟩
      left_inv := fun x ↦ Subtype.ext (HurwitzPrymRex_Bar.ext rfl)
      right_inv := fun x ↦ Subtype.ext rfl
      map_add' := fun x y ↦ Subtype.ext rfl }
  have hr := rank_eq_of_equiv_equiv (fun c : ℂ ↦ star c) j
    (Function.Involutive.bijective (f := fun c : ℂ ↦ star c) star_star)
    (fun _ _ ↦ rfl)
  have hf : Module.finrank ℂ (LinearMap.range B) = Module.finrank ℂ (LinearMap.range A) := by
    simp only [Module.finrank, hr]
  exact hf.trans b63d_naturalRep_projector_rank

end HodgeLean.Foundations.Program
