import HodgeLean.Foundations.Abdulali.DeterminantPolarization

noncomputable section
open HodgeLean.Foundations InvariantsExterior
open scoped TensorProduct
namespace HodgeLean.Foundations.Abdulali

/-- Exterior projection commutes with the tensor power of any linear map.
Source: universal property of exterior powers; Weyl, The Classical Groups,
Chapter II, §9. -/
theorem wedgeQuotient_map {V M : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup M] [Module ℂ M] (n : ℕ) (f : V →ₗ[ℂ] M) :
    (wedgeQuotient n).comp (PiTensorProduct.map (fun _ : Fin n => f)) =
      (exteriorPower.map n f).comp (wedgeQuotient n) := by
  ext v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    PiTensorProduct.map_tprod, wedgeQuotient_tprod, exteriorPower.map_apply_ιMulti,
    Function.comp_def]

/-- The exterior power of a linear family is a homogeneous polynomial family:
its evaluations at rational parameter vectors span all complex evaluations,
for an arbitrary fixed exterior input.
Source: Weyl, The Classical Groups, Chapter II, §9, polarization;
Goodman–Wallach, Symmetry, Representations, and Invariants, Chapter 4. -/
theorem exterior_map_mem_span_rational_parameters
    {V M : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    {n m : ℕ} (F : (Fin m → ℂ) →ₗ[ℂ] (V →ₗ[ℂ] M))
    (u : ⋀[ℂ]^n V) (a : Fin m → ℂ) :
    exteriorPower.map n (F a) u ∈ Submodule.span ℂ
      (Set.range (fun b : Fin m → ℚ =>
        exteriorPower.map n (F (fun i => (b i : ℂ))) u)) := by
  classical
  let t := (n.factorial : ℂ)⁻¹ • exteriorPower.toTensorPower ℂ V n u
  let g := ((wedgeQuotient n).comp (LinearMap.applyₗ t)).compMultilinearMap
    ((PiTensorProduct.mapMultilinear ℂ (fun _ : Fin n => V) (fun _ : Fin n => M)).compLinearMap
      (fun _ => F))
  have ht : wedgeQuotient n t = u := by
    rw [show t = (n.factorial : ℂ)⁻¹ • exteriorPower.toTensorPower ℂ V n u from rfl,
      map_smul, wedgeQuotient_toTensorPower, smul_smul, inv_mul_cancel₀, one_smul]
    exact_mod_cast n.factorial_ne_zero
  have hg (b : Fin m → ℂ) : g (fun _ => b) = exteriorPower.map n (F b) u := by
    change wedgeQuotient n (PiTensorProduct.map (fun _ : Fin n => F b) t) = _
    have h := LinearMap.congr_fun (wedgeQuotient_map n (F b)) t
    simpa only [LinearMap.comp_apply, ht] using h
  have h := multilinear_diagonal_mem_span_rat g a
  simpa only [hg] using h

end HodgeLean.Foundations.Abdulali
