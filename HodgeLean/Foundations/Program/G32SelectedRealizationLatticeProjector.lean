import HodgeLean.Foundations.Program.G32SelectedRealizationSaturation

noncomputable section
set_option maxRecDepth 2000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem g32y_integral_image_projector {H M : Type*} [Group H] [Fintype H]
    [AddCommGroup M] [Module.Free ℤ M] (R : Representation ℤ H M) (c : H → ℤ) :
    ∃ N : ℕ, 0 < N ∧ ∃ z : H → ℤ,
      let T : Module.End ℤ M := ∑ h, z h • R h
      (∀ x, T (T x) = (N : ℤ) • T x) ∧
        b63l_saturation (LinearMap.range T) =
          b63l_saturation (LinearMap.range (∑ h, c h • R h)) := by
  classical
  let : NeZero (Nat.card H : ℚ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  let RQ : Representation ℚ H (ℚ ⊗[ℤ] M) :=
    (Module.End.baseChangeHom ℤ ℚ M).toMonoidHom.comp R
  let ρ := RQ.asAlgebraHom
  let p : MonoidAlgebra ℚ H := ∑ h, MonoidAlgebra.single h (c h : ℚ)
  obtain ⟨e, he, hRe⟩ := g32y_projector_with_range ρ.toRingHom p
  let u : H → ℚ := e.coeff
  have hsum : ρ e = ∑ h, u h • RQ h := by
    change RQ.asAlgebraHom e = _
    rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
    exact Finsupp.sum_fintype _ _ (fun h ↦ zero_smul ℚ (RQ h))
  obtain ⟨N, hN, z, hz⟩ := g32y_clear_denominators u
  let T : Module.End ℤ M := ∑ h, z h • R h
  let P : Module.End ℤ M := ∑ h, c h • R h
  have hTQ : T.baseChange ℚ = (N : ℚ) • ρ e := by
    change (Module.End.baseChangeHom ℤ ℚ M) (∑ h, z h • R h) = _
    rw [map_sum, hsum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [map_smul, smul_smul, hz, Int.cast_smul_eq_zsmul]
    rfl
  have hPQ : P.baseChange ℚ = ρ p := by
    change (Module.End.baseChangeHom ℤ ℚ M) (∑ h, c h • R h) =
      RQ.asAlgebraHom (∑ h, MonoidAlgebra.single h (c h : ℚ))
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [map_smul, Representation.asAlgebraHom_single, Int.cast_smul_eq_zsmul]
    rfl
  have hscaled : T.baseChange ℚ ∘ₗ T.baseChange ℚ = (N : ℚ) • T.baseChange ℚ := by
    rw [hTQ, LinearMap.smul_comp, LinearMap.comp_smul, ← Module.End.mul_eq_comp,
      ← map_mul, he]
  have hsq (x : M) : T (T x) = (N : ℤ) • T x := by
    apply g32y_rat_tmul_injective
    have hh := LinearMap.congr_fun hscaled ((1 : ℚ) ⊗ₜ[ℤ] x)
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.smul_apply] at hh
    change (1 : ℚ) ⊗ₜ[ℤ] T (T x) = (1 : ℚ) ⊗ₜ[ℤ] ((N : ℤ) • T x)
    rw [TensorProduct.tmul_smul, ← Int.cast_smul_eq_zsmul ℚ]
    simpa only [Int.cast_natCast] using hh
  have hRange : LinearMap.range (T.baseChange ℚ) = LinearMap.range (P.baseChange ℚ) := by
    rw [hTQ, hPQ, LinearMap.range_smul _ _ (by exact_mod_cast hN.ne')]
    exact hRe
  refine ⟨N, hN, z, hsq, ?_⟩
  ext x
  rw [g32y_mem_saturation_range_iff, g32y_mem_saturation_range_iff, hRange]

end HodgeLean.Foundations.Program
