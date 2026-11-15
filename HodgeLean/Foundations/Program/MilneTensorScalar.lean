import HodgeLean.Foundations.Program.MilneTensorProducts

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem m1b_products_top_even : ∀ (n : ℕ), Even n →
    m1b_products (⊤ : Submodule ℂ (⨂[ℂ]^2 V)) n = ⊤ := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro _; rfl
  | one => intro h; obtain ⟨k, hk⟩ := h; omega
  | more n ih _ =>
    intro hn
    have hn' : Even n := by
      obtain ⟨k, hk⟩ := hn
      exact ⟨k - 1, by omega⟩
    apply top_unique
    intro t ht
    clear ht
    obtain ⟨w, rfl⟩ := (InvariantsExterior.tensorAppend n 2 (K := ℂ) (M := V)).surjective t
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | tmul a b =>
      apply Submodule.subset_span
      refine ⟨1, a, b, ?_, Submodule.mem_top, ?_⟩
      · rw [ih hn']; exact Submodule.mem_top
      · simp only [map_one, Module.End.one_apply]
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy

theorem m1b_fixed_even_scalar_signs (S : Set (Module.End ℂ V))
    (hS : ∀ u ∈ S, u = 1 ∨ u = -1) (n : ℕ) (hn : Even n) :
    m1b_fixed S n = ⊤ := by
  apply top_unique
  intro t _
  simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  intro u hu
  rcases hS u hu with rfl | rfl
  · rw [SchurWeyl.tensorPow_one, Module.End.one_apply]
  · have hscalar : (-1 : Module.End ℂ V) = (-1 : ℂ) • 1 := by simp
    rw [hscalar, SchurWeyl.tensorPow_smul_one, Fintype.card_fin,
      hn.neg_one_pow, one_smul, Module.End.one_apply]

theorem m1b_line_isometries (B : LinearMap.BilinForm ℂ ℂ) (hB : B.Nondegenerate)
    (u : Module.End ℂ ℂ) (hu : u ∈ m1b_isometries B) : u = 1 ∨ u = -1 := by
  have hb : B 1 1 ≠ 0 := by
    intro h
    have hz (y : ℂ) : B 1 y = 0 := by
      calc B 1 y = B 1 (y • (1 : ℂ)) := by rw [smul_eq_mul, mul_one]
           _ = 0 := by rw [map_smul, h, smul_zero]
    exact one_ne_zero (hB.1 1 hz)
  have hu_scalar (x : ℂ) : u x = x * u 1 := by
    have h := u.map_smul x (1 : ℂ)
    simpa only [smul_eq_mul, mul_one] using h
  have hb_scalar (x y : ℂ) : B x y = x * y * B 1 1 := by
    have hx : B x = x • B 1 := by simpa using B.map_smul x (1 : ℂ)
    have hy : B 1 y = y * B 1 1 := by simpa using (B 1).map_smul y (1 : ℂ)
    rw [hx, LinearMap.smul_apply, hy, smul_eq_mul]
    ring
  have he := hu.2 1 1
  rw [hb_scalar] at he
  have hs : u 1 * u 1 = 1 := mul_right_cancel₀ hb (by simpa using he)
  rcases mul_self_eq_one_iff.mp hs with h | h
  · left
    apply LinearMap.ext
    intro x
    rw [hu_scalar, h, mul_one]
    rfl
  · right
    apply LinearMap.ext
    intro x
    rw [hu_scalar, h, mul_neg_one]
    rfl

theorem m1b_orthogonal_line_tensors (B : LinearMap.BilinForm ℂ ℂ)
    (hB : B.Nondegenerate) (r n : ℕ) :
    m1b_fixed (m1b_copies r '' m1b_isometries B) n =
      m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries B) 2) n := by
  have hS : ∀ u ∈ m1b_copies r '' m1b_isometries B,
      u = 1 ∨ u = -1 := by
    rintro u ⟨v, hv, rfl⟩
    rcases m1b_line_isometries B hB v hv with rfl | rfl
    · left
      ext x i
      rfl
    · exact Or.inr (m1b_copies_neg_one r)
  by_cases hn : Even n
  · rw [m1b_fixed_even_scalar_signs _ hS n hn,
      m1b_fixed_even_scalar_signs _ hS 2 (by decide), m1b_products_top_even n hn]
  · exact m1b_isometry_tensors_odd B r n (Nat.not_even_iff_odd.mp hn)

theorem m1b_tensor_zero_of_subsingleton [Subsingleton V] (n : ℕ)
    (t : ⨂[ℂ]^(n + 1) V) : t = 0 := by
  have h : (LinearMap.id : (⨂[ℂ]^(n + 1) V) →ₗ[ℂ] (⨂[ℂ]^(n + 1) V)) = 0 := by
    ext v
    exact (PiTensorProduct.tprod ℂ).map_coord_zero (0 : Fin (n + 1))
      (Subsingleton.elim _ _)
  exact LinearMap.congr_fun h t

theorem m1b_generation_subsingleton [Subsingleton V]
    (S : Set (Module.End ℂ V)) (n : ℕ) :
    m1b_fixed S n = m1b_products (m1b_fixed S 2) n := by
  cases n with
  | zero => exact m1b_tensor_generation_degree_zero S
  | succ n =>
    ext t
    rw [m1b_tensor_zero_of_subsingleton n t]
    exact iff_of_true (Submodule.zero_mem _) (Submodule.zero_mem _)

end HodgeLean.Foundations.Program
