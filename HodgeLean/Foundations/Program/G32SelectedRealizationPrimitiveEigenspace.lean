import HodgeLean.Foundations.Program.G32SelectedRealizationPrimitiveEigenLift
import HodgeLean.Foundations.Program.G32SelectedRealizationEigenGenerator

noncomputable section
open HodgeLean.Foundations
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem g32y_primitive_character_eigenspace {U : Type*} [AddCommGroup U] [Module ℚ U]
    (S : g32p_Supplier) (T : S.H → Module.End ℚ U) (W : Submodule ℚ U)
    (hW : W = (⨅ (h : S.H) (_ : S.χ h = 1), LinearMap.eqLocus (T h) LinearMap.id) ⊓
      ⨅ (h : S.H) (_ : S.χ h = Multiplicative.ofAdd 1),
        LinearMap.ker (Polynomial.aeval (T h) (Polynomial.cyclotomic S.m ℚ)))
    {d : ℕ} (e : W ≃ₗ[ℚ] (Fin d → cyc_Field S.m))
    (he : ∀ h, W.subtype ∘ₗ cyc_scalar e (g32p_fieldValue S h) = T h ∘ₗ W.subtype)
    (σ : cyc_Field S.m →ₐ[ℚ] ℂ) :
    (cyc_eigenspace e σ).map (W.subtype.baseChange ℂ) =
      ⨅ h : S.H, Module.End.eigenspace ((T h).baseChange ℂ) (σ (g32p_fieldValue S h)) := by
  have hc (h : S.H) : W.subtype.baseChange ℂ ∘ₗ
      (cyc_scalar e (g32p_fieldValue S h)).baseChange ℂ =
        (T h).baseChange ℂ ∘ₗ W.subtype.baseChange ℂ := by
    simpa only [LinearMap.baseChange_comp] using congrArg (LinearMap.baseChange ℂ) (he h)
  have hinj : Function.Injective (W.subtype.baseChange ℂ) :=
    Module.Flat.lTensor_preserves_injective_linearMap W.subtype Subtype.val_injective
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    apply (Submodule.mem_iInf _).mpr
    intro h
    apply Module.End.mem_eigenspace_iff.mpr
    have hs := Module.End.mem_eigenspace_iff.mp
      ((Submodule.mem_iInf _).mp hw (g32p_fieldValue S h))
    have hh := LinearMap.congr_fun (hc h) w
    change W.subtype.baseChange ℂ
      ((cyc_scalar e (g32p_fieldValue S h)).baseChange ℂ w) =
        (T h).baseChange ℂ (W.subtype.baseChange ℂ w) at hh
    rw [hs, map_smul] at hh
    exact hh.symm
  · intro v hv
    have hvv (h : S.H) : (T h).baseChange ℂ v = σ (g32p_fieldValue S h) • v :=
      Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv h)
    have hmem : v ∈ LinearMap.range (W.subtype.baseChange ℂ) := by
      rw [hW]
      exact g32y_primitive_character_eigenvector_lift S.three_le S.χ T σ v hvv
    obtain ⟨w, hw⟩ := hmem
    refine ⟨w, ?_, hw⟩
    rw [g32y_cyclotomic_eigenspace_generator]
    apply Module.End.mem_eigenspace_iff.mpr
    apply hinj
    rw [map_smul]
    obtain ⟨a, ha⟩ := S.surjective (Multiplicative.ofAdd 1)
    have hfa : g32p_fieldValue S a = IsCyclotomicExtension.zeta S.m ℚ (cyc_Field S.m) := by
      simp only [g32p_fieldValue, ha, toAdd_ofAdd,
        ZMod.val_one'' (n := S.m) (by have := S.three_le; omega), pow_one]
      rfl
    rw [← hfa]
    exact (LinearMap.congr_fun (hc a) w).trans (by
      change (T a).baseChange ℂ (W.subtype.baseChange ℂ w) =
        σ (g32p_fieldValue S a) • W.subtype.baseChange ℂ w
      rw [hw]
      exact hvv a)

end HodgeLean.Foundations.Program
