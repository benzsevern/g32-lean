import HodgeLean.Foundations.Program.G32SelectedRealizationReference

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem g32y_tensor_integer_multiple {M : Type*} [AddCommGroup M]
    (v : ℚ ⊗[ℤ] M) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ x : M, n • v = (1 : ℚ) ⊗ₜ[ℤ] x := by
  induction v using TensorProduct.inductionOn with
  | tmul q x =>
    refine ⟨q.den, ?_, q.num • x, ?_⟩
    · exact_mod_cast q.den_pos.ne'
    · simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul', zsmul_eq_mul,
        Int.cast_natCast, Rat.den_mul_eq_num, mul_one]
  | add v w hv hw =>
    obtain ⟨n, hn, x, hx⟩ := hv
    obtain ⟨m, hm, y, hy⟩ := hw
    refine ⟨n * m, mul_ne_zero hn hm, m • x + n • y, ?_⟩
    calc
      (n * m) • (v + w) = m • (n • v) + n • (m • w) := by
        simp only [smul_add, mul_smul]
        rw [smul_comm n m v]
      _ = m • ((1 : ℚ) ⊗ₜ[ℤ] x) + n • ((1 : ℚ) ⊗ₜ[ℤ] y) := by rw [hx, hy]
      _ = (1 : ℚ) ⊗ₜ[ℤ] (m • x + n • y) := by
        rw [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul]

theorem g32y_rat_tmul_injective {M : Type*} [AddCommGroup M] [Module.Free ℤ M] :
    Function.Injective (fun x : M ↦ (1 : ℚ) ⊗ₜ[ℤ] x) := by
  let b := Module.Free.chooseBasis ℤ M
  intro x y hxy
  refine b.repr.injective (Finsupp.ext fun i ↦ ?_)
  have hh := congrArg (fun v ↦ (b.baseChange ℚ).repr v i) hxy
  simp only [Module.Basis.baseChange_repr_tmul, zsmul_eq_mul, mul_one] at hh
  exact_mod_cast hh

theorem g32y_mem_saturation_range_iff {M : Type*} [AddCommGroup M] [Module.Free ℤ M]
    (f : M →ₗ[ℤ] M) (x : M) :
    x ∈ b63l_saturation (LinearMap.range f) ↔
      (1 : ℚ) ⊗ₜ[ℤ] x ∈ LinearMap.range (f.baseChange ℚ) := by
  constructor
  · rintro ⟨n, hn, y, hy⟩
    have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    refine ⟨(n : ℚ)⁻¹ • ((1 : ℚ) ⊗ₜ[ℤ] y), ?_⟩
    rw [map_smul, LinearMap.baseChange_tmul, hy, TensorProduct.tmul_smul,
      ← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ hnQ, one_smul]
  · rintro ⟨v, hv⟩
    obtain ⟨n, hn, y, hy⟩ := g32y_tensor_integer_multiple v
    refine ⟨n, hn, y, ?_⟩
    apply g32y_rat_tmul_injective
    calc
      (1 : ℚ) ⊗ₜ[ℤ] f y = f.baseChange ℚ ((1 : ℚ) ⊗ₜ[ℤ] y) :=
        rfl
      _ = (1 : ℚ) ⊗ₜ[ℤ] (n • x) := by
        rw [← hy, map_zsmul, hv, ← TensorProduct.tmul_smul]

theorem g32y_scaled_on_saturation {M : Type*} [AddCommGroup M] [Module.Free ℤ M]
    (T : M →ₗ[ℤ] M) (N : ℤ) (hT : ∀ x, T (T x) = N • T x)
    (v : M) (hv : v ∈ b63l_saturation (LinearMap.range T)) : T v = N • v := by
  obtain ⟨n, hn, y, hy⟩ := hv
  apply smul_right_injective M hn
  calc
    n • T v = T (n • v) := (map_smul T n v).symm
    _ = T (T y) := by rw [hy]
    _ = N • T y := hT y
    _ = n • (N • v) := by rw [hy, smul_comm N n v]

theorem g32y_saturated_projection {M : Type*} [AddCommGroup M] [Module.Free ℤ M]
    (T : M →ₗ[ℤ] M) (N : ℤ) (hT : ∀ x, T (T x) = N • T x) :
    ∃ q : M →ₗ[ℤ] b63l_saturation (LinearMap.range T),
      (b63l_saturation (LinearMap.range T)).subtype ∘ₗ q = T ∧
        q ∘ₗ (b63l_saturation (LinearMap.range T)).subtype = N • LinearMap.id := by
  let q := T.codRestrict (b63l_saturation (LinearMap.range T))
    (fun x ↦ ⟨1, one_ne_zero, ⟨x, by rw [one_smul]⟩⟩)
  refine ⟨q, rfl, ?_⟩
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact g32y_scaled_on_saturation T N hT v v.property

theorem g32y_saturated_marking_retraction {L M : Type*} [AddCommGroup L] [AddCommGroup M]
    [Module.Free ℤ M] (T : M →ₗ[ℤ] M) (N : ℤ) (hT : ∀ x, T (T x) = N • T x)
    (E : L ≃ₗ[ℤ] b63l_saturation (LinearMap.range T)) :
    ∃ p : M →ₗ[ℤ] L,
      (b63l_saturation (LinearMap.range T)).subtype ∘ₗ E.toLinearMap ∘ₗ p = T ∧
        p ∘ₗ (b63l_saturation (LinearMap.range T)).subtype ∘ₗ E.toLinearMap = N • LinearMap.id := by
  obtain ⟨q, hq, hret⟩ := g32y_saturated_projection T N hT
  let p := E.symm.toLinearMap ∘ₗ q
  refine ⟨p, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    change (E (E.symm (q x))).val = T x
    rw [E.apply_symm_apply]
    exact LinearMap.congr_fun hq x
  · apply LinearMap.ext
    intro x
    apply E.injective
    change E (E.symm (q (E x).val)) = E (N • x)
    rw [E.apply_symm_apply, map_smul]
    exact LinearMap.congr_fun hret (E x)

end HodgeLean.Foundations.Program
