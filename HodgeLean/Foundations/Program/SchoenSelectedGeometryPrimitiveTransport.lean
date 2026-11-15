import HodgeLean.Foundations.Program.SchoenSelectedGeometryPrimitiveRange
import HodgeLean.Foundations.Program.SchoenSelectedGeometryCyclotomicKernel

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- An equivariant comparison transports quotient primitive kernels to character relations. -/
theorem s0_primitive_transport_range
    {H J C Y : Type*} [Group H]
    [AddCommGroup J] [Module ℚ J] [AddCommGroup C] [Module ℚ C]
    [AddCommGroup Y] [Module ℚ Y] {m : ℕ} [NeZero m]
    (χ : H →* Multiplicative (ZMod m)) (hχ : Function.Surjective χ)
    (j : J ≃ₗ[ℚ] C) (q : Y →ₗ[ℚ] C) (hq : Function.Injective q)
    (R : H → Module.End ℚ J) (A : H → Module.End ℚ C)
    (B U : Module.End ℚ Y) (hBU : B * U = 1) (hUB : U * B = 1)
    (hj : ∀ h, j.toLinearMap ∘ₗ R h = A h ∘ₗ j.toLinearMap)
    (hi : ∀ c, c ∈ LinearMap.range q ↔ ∀ h, χ h = 1 → A h c = c)
    (he : ∀ h, χ h = Multiplicative.ofAdd 1 → q ∘ₗ U = A h ∘ₗ q) :
    (LinearMap.ker (Polynomial.aeval B (Polynomial.cyclotomic m ℚ))).map q =
      ((⨅ h, ⨅ (_ : χ h = 1), LinearMap.eqLocus (R h) LinearMap.id) ⊓
        ⨅ h, ⨅ (_ : χ h = Multiplicative.ofAdd 1),
          LinearMap.ker (Polynomial.aeval (R h) (Polynomial.cyclotomic m ℚ))).map j.toLinearMap := by
  let qJ := j.symm.toLinearMap ∘ₗ q
  have hqJ : Function.Injective qJ := j.symm.injective.comp hq
  have hqJval (y : Y) : j (qJ y) = q y := j.apply_symm_apply (q y)
  have hr : LinearMap.range qJ =
      ⨅ h, ⨅ (_ : χ h = 1), LinearMap.eqLocus (R h) LinearMap.id := by
    ext x
    simp only [Submodule.mem_iInf, LinearMap.mem_eqLocus, LinearMap.id_apply]
    constructor
    · rintro ⟨y, rfl⟩ h hh
      apply j.injective
      have hv := (hi (q y)).mp (LinearMap.mem_range_self q y) h hh
      have hc := LinearMap.congr_fun (hj h) (qJ y)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hqJval] at hc
      exact hc.trans (hv.trans (hqJval y).symm)
    · intro hx
      have hv : j x ∈ LinearMap.range q := by
        apply (hi (j x)).mpr
        intro h hh
        have hc := LinearMap.congr_fun (hj h) x
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hx h hh] at hc
        exact hc.symm
      obtain ⟨y, hy⟩ := hv
      refine ⟨y, j.injective ?_⟩
      exact (hqJval y).trans hy
  have heJ : ∀ h, χ h = Multiplicative.ofAdd 1 → qJ ∘ₗ U = R h ∘ₗ qJ := by
    intro h hh
    ext y
    apply j.injective
    have hc := LinearMap.congr_fun (hj h) (qJ y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hqJval] at hc
    change j (qJ (U y)) = j (R h (qJ y))
    rw [hqJval, hc]
    exact LinearMap.congr_fun (he h hh) y
  have hp := s0_primitive_pullback_range χ hχ R U qJ hqJ hr heJ
  rw [s0_cyclotomic_inverse_kernel B U hBU hUB]
  rw [← hp, ← Submodule.map_comp]
  congr 1
  ext y
  exact (hqJval y).symm

#print axioms s0_primitive_transport_range
end HodgeLean.Foundations.Program
