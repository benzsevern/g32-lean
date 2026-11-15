import HodgeLean.Foundations.Program.MilneTensorProducts

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem m1b_products_perm (Q : Submodule ℂ (⨂[ℂ]^2 V)) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (t : ⨂[ℂ]^n V) (ht : t ∈ m1b_products Q n) :
    SchurWeyl.permRep ℂ V (Fin n) σ t ∈ m1b_products Q n := by
  rcases n with _ | _ | n
  · exact Submodule.mem_top
  · have hzero : t = 0 := ht
    rw [hzero, map_zero]
    exact Submodule.zero_mem _
  · change t ∈ Submodule.span ℂ _ at ht
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨τ, a, b, ha, hb, rfl⟩ := hx
      apply Submodule.subset_span
      refine ⟨σ * τ, a, b, ha, hb, ?_⟩
      rw [map_mul, Module.End.mul_apply]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
    | smul c x hx ihx =>
      rw [map_smul]
      exact Submodule.smul_mem _ c ihx

theorem m1b_products_span_perm (Q : Submodule ℂ (⨂[ℂ]^2 V)) (n : ℕ)
    (F : Module.End ℂ (⨂[ℂ]^n V))
    (hF : F ∈ Submodule.span ℂ (Set.range (SchurWeyl.permRep ℂ V (Fin n))))
    (t : ⨂[ℂ]^n V) (ht : t ∈ m1b_products Q n) : F t ∈ m1b_products Q n := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨σ, rfl⟩ := hF
    exact m1b_products_perm Q n σ t ht
  | zero => exact Submodule.zero_mem _
  | add F G hF hG ihF ihG => exact Submodule.add_mem _ ihF ihG
  | smul c F hF ihF => exact Submodule.smul_mem _ c ihF

theorem m1b_products_commutant [FiniteDimensional ℂ V]
    (Q : Submodule ℂ (⨂[ℂ]^2 V)) (n : ℕ) (F : Module.End ℂ (⨂[ℂ]^n V))
    (hF : ∀ g : LinearMap.GeneralLinearGroup ℂ V,
      SchurWeyl.tensorPow (Fin n) (g : Module.End ℂ V) * F =
        F * SchurWeyl.tensorPow (Fin n) (g : Module.End ℂ V))
    (t : ⨂[ℂ]^n V) (ht : t ∈ m1b_products Q n) : F t ∈ m1b_products Q n := by
  have hmem : F ∈ Subalgebra.toSubmodule (Subalgebra.centralizer ℂ
      (Set.range fun g : LinearMap.GeneralLinearGroup ℂ V =>
        SchurWeyl.tensorPow (Fin n) (g : Module.End ℂ V))) := by
    rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    exact hF g
  rw [SchurWeyl.centralizer_tensorPow_units_eq_span_permRep] at hmem
  exact m1b_products_span_perm Q n F hmem t ht

end HodgeLean.Foundations.Program
