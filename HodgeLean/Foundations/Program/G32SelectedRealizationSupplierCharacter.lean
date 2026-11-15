import HodgeLean.Foundations.Program.G32SelectedRealizationPrimitiveHodge

noncomputable section
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

theorem g32y_fieldValue_mul (S : g32p_Supplier) (a b : S.H) :
    g32p_fieldValue S (a * b) = g32p_fieldValue S a * g32p_fieldValue S b := by
  have hz := IsCyclotomicExtension.zeta_spec S.m ℚ (cyc_Field S.m)
  simp only [g32p_fieldValue, map_mul, toAdd_mul, ZMod.val_add,
    ← pow_add]
  have he : S.m = orderOf (g32p_zeta S) := hz.eq_orderOf
  have hm (n : ℕ) : g32p_zeta S ^ (n % S.m) = g32p_zeta S ^ n := by
    simpa only [← he] using pow_mod_orderOf (g32p_zeta S) n
  exact hm _

theorem g32y_supplier_complex_character (S : g32p_Supplier)
    (σ : cyc_Field S.m →ₐ[ℚ] ℂ) :
    ∃ χ : S.H →* ℂˣ, (∀ h, (χ h : ℂ) = σ (g32p_fieldValue S h)) ∧
      ∃ h, χ h ≠ 1 := by
  have hz := IsCyclotomicExtension.zeta_spec S.m ℚ (cyc_Field S.m)
  have hn : ∀ h : S.H, σ (g32p_fieldValue S h) ≠ 0 := by
    intro h
    apply (map_ne_zero σ).mpr
    exact pow_ne_zero _ (hz.ne_zero (NeZero.ne S.m))
  let χ : S.H →* ℂˣ := {
    toFun := fun h ↦ Units.mk0 (σ (g32p_fieldValue S h)) (hn h)
    map_one' := by apply Units.ext; simp [g32p_fieldValue]
    map_mul' := by intro a b; apply Units.ext; simp [g32y_fieldValue_mul] }
  refine ⟨χ, fun _ ↦ rfl, ?_⟩
  obtain ⟨h, hh⟩ := S.surjective (Multiplicative.ofAdd 1)
  refine ⟨h, ?_⟩
  intro he
  have hv := congrArg (fun u : ℂˣ ↦ (u : ℂ)) he
  change σ (g32p_fieldValue S h) = 1 at hv
  have hval : g32p_fieldValue S h = g32p_zeta S := by
    simp only [g32p_fieldValue, hh, toAdd_ofAdd]
    rw [ZMod.val_one'' (n := S.m) (by have := S.three_le; omega), pow_one]
  rw [hval, ← map_one σ] at hv
  exact hz.ne_one (by have := S.three_le; omega) (σ.injective hv)

end HodgeLean.Foundations.Program
