import HodgeLean.Foundations.PositivePolarizationDefs

/-! # Linear algebra for positive polarizations

Helper lemmas for `PositivePolarizationProofs.lean` (lane `p1l_`): the real contraction
`p1_realContract ω` is alternating, it intertwines transposes of base-changed maps, and a nonzero
operator `K` with an adjoint `K'` for a positive definite symmetric form has `0 < tr (K' ∘ K)`.
-/

noncomputable section

open Module
open scoped TensorProduct
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations

section Trace

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ W] in
/-- For an orthogonal basis, the `i`-th coordinate of `x` times `S (v i) (v i)` is `S x (v i)`. -/
theorem p1l_repr_mul_self {S : LinearMap.BilinForm ℝ W} {n : Type*} [Fintype n]
    (v : Basis n ℝ W) (hv : S.IsOrthoᵢ v) (x : W) (i : n) :
    v.repr x i * S (v i) (v i) = S x (v i) := by
  classical
  conv_rhs => rw [← v.sum_repr x]
  rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hv hj]
  · simp

/-- **Positivity of `tr (K' K)`.** If `S` is a positive definite symmetric bilinear form on a
finite-dimensional real space, `K'` is an `S`-adjoint of `K` and `K ≠ 0`, then `0 < tr (K' ∘ K)`:
in an `S`-orthogonal basis the diagonal entries are `S (K vᵢ, K vᵢ) / S (vᵢ, vᵢ) ≥ 0`, and one
of them is positive. -/
theorem p1l_trace_pos_of_adjoint {S : LinearMap.BilinForm ℝ W} (hS : S.IsSymm)
    (hpos : ∀ x, x ≠ 0 → 0 < S x x) {K K' : W →ₗ[ℝ] W} (hK : ∀ x y, S (K x) y = S x (K' y))
    (hK0 : K ≠ 0) : 0 < LinearMap.trace ℝ W (K' ∘ₗ K) := by
  classical
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.BilinForm.isSymm_iff.1 hS)
  have hvv : ∀ i, 0 < S (v i) (v i) := fun i => hpos _ (v.ne_zero i)
  have hterm : ∀ i, v.repr ((K' ∘ₗ K) (v i)) i = S (K (v i)) (K (v i)) / S (v i) (v i) := by
    intro i
    rw [eq_div_iff (hvv i).ne', p1l_repr_mul_self v hv, LinearMap.comp_apply, hS.eq, ← hK]
  rw [LinearMap.trace_eq_matrix_trace ℝ v, Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, hterm]
  refine Finset.sum_pos' (fun i _ => div_nonneg ?_ (hvv i).le) ?_
  · by_cases h : K (v i) = 0
    · simp [h]
    · exact (hpos _ h).le
  · by_contra hall
    push Not at hall
    apply hK0
    refine v.ext fun i => ?_
    by_contra h
    exact absurd (hall i (Finset.mem_univ _)) (not_le.2 (div_pos (hpos _ h) (hvv i)))

end Trace

section Real

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-- Mathlib's identification `ℝ ⊗ V^∨ ≃ (ℝ ⊗ V)^∨`.
Source: Bourbaki, *Algebra I*, Ch. II, §5 (extension of scalars of duals); Mathlib
`IsBaseChange.toDualBaseChange`. -/
abbrev p1l_e (V : Type*) [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V] :
    ℝ ⊗[ℚ] Dual ℚ V ≃ₗ[ℝ] Dual ℝ (ℝ ⊗[ℚ] V) :=
  (TensorProduct.isBaseChange ℚ V ℝ).toDualBaseChange

theorem p1l_e_tmul (a : ℝ) (φ : Dual ℚ V) (v : V) :
    p1l_e V (a ⊗ₜ φ) (1 ⊗ₜ v) = a * algebraMap ℚ ℝ (φ v) :=
  (TensorProduct.isBaseChange ℚ V ℝ).toDualBaseChange_tmul a φ v

/-- On `ℚ¹`, `1 ⊗ id` is the functional `1 ⊗ q ↦ q`. -/
example (q : ℚ) : p1l_e ℚ (1 ⊗ₜ LinearMap.id) (1 ⊗ₜ q) = q := by
  rw [p1l_e_tmul]; simp

omit [Module.Finite ℚ V] in
/-- Real functionals on `ℝ ⊗ V` agree when they agree on `1 ⊗ v`. -/
theorem p1l_dual_ext {φ ψ : Dual ℝ (ℝ ⊗[ℚ] V)} (h : ∀ v : V, φ (1 ⊗ₜ v) = ψ (1 ⊗ₜ v)) :
    φ = ψ := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul r v =>
    have : r ⊗ₜ[ℚ] v = r • ((1 : ℝ) ⊗ₜ[ℚ] v) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, map_smul, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem p1l_realContract_e (ω : ⋀[ℚ]^2 V) (a : ℝ ⊗[ℚ] Dual ℚ V) :
    p1_realContract ω (p1l_e V a) = (contract ω).baseChange ℝ a := by
  simp [p1_realContract]

/-- The transpose of a base-changed map, read through `ℝ ⊗ V^∨ ≃ (ℝ ⊗ V)^∨`. -/
theorem p1l_dualMap_baseChange_e (f : Module.End ℚ V) (a : ℝ ⊗[ℚ] Dual ℚ V) :
    (f.baseChange ℝ).dualMap (p1l_e V a) = p1l_e V ((f.dualMap).baseChange ℝ a) := by
  induction a using TensorProduct.inductionOn with
  | tmul r φ =>
    refine p1l_dual_ext fun v => ?_
    rw [LinearMap.dualMap_apply, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      p1l_e_tmul, p1l_e_tmul, LinearMap.dualMap_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- `B_ω` over `ℝ` on rational functionals: `(a ⊗ ψ) (c (b ⊗ φ)) = a b ψ (c φ)`. -/
theorem p1l_e_realContract_tmul (ω : ⋀[ℚ]^2 V) (a b : ℝ) (φ ψ : Dual ℚ V) :
    p1l_e V (a ⊗ₜ ψ) (p1_realContract ω (p1l_e V (b ⊗ₜ φ))) =
      a * b * algebraMap ℚ ℝ (ψ (contract ω φ)) := by
  rw [p1l_realContract_e, LinearMap.baseChange_tmul]
  have : b ⊗ₜ[ℚ] contract ω φ = b • ((1 : ℝ) ⊗ₜ[ℚ] contract ω φ) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [this, map_smul, p1l_e_tmul, smul_eq_mul]
  ring

omit [Module.Finite ℚ V] in
/-- `B_ω` over `ℚ` is skew. -/
theorem p1l_contract_skew (ω : ⋀[ℚ]^2 V) (φ ψ : Dual ℚ V) :
    ψ (contract ω φ) = -φ (contract ω ψ) := by
  have h := apply_contract_self ω (φ + ψ)
  simp only [map_add, LinearMap.add_apply, apply_contract_self, zero_add, add_zero] at h
  linear_combination h

/-- **`B_ω` over `ℝ` is skew**: `ψ (c_ℝ φ) = -φ (c_ℝ ψ)`. -/
theorem p1l_realContract_skew (ω : ⋀[ℚ]^2 V) (φ ψ : Dual ℝ (ℝ ⊗[ℚ] V)) :
    ψ (p1_realContract ω φ) = -φ (p1_realContract ω ψ) := by
  obtain ⟨a, rfl⟩ := (p1l_e V).surjective φ
  obtain ⟨b, rfl⟩ := (p1l_e V).surjective ψ
  induction a using TensorProduct.inductionOn with
  | tmul r φ₀ =>
    induction b using TensorProduct.inductionOn with
    | tmul s ψ₀ =>
      rw [p1l_e_realContract_tmul, p1l_e_realContract_tmul, p1l_contract_skew ω φ₀ ψ₀]
      push_cast
      ring
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, neg_add]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, neg_add]

/-- `B_ω` over `ℝ` is alternating. -/
theorem p1l_realContract_self (ω : ⋀[ℚ]^2 V) (φ : Dual ℝ (ℝ ⊗[ℚ] V)) :
    φ (p1_realContract ω φ) = 0 := by
  have := p1l_realContract_skew ω φ φ
  linarith

/-- The real contraction intertwines transposes: if `c ∘ fᵀ = g ∘ c`, then
`c_ℝ ∘ f_ℝᵀ = g_ℝ ∘ c_ℝ`. -/
theorem p1l_realContract_dualMap (ω : ⋀[ℚ]^2 V) {f g : Module.End ℚ V}
    (h : contract ω ∘ₗ f.dualMap = g ∘ₗ contract ω) (φ : Dual ℝ (ℝ ⊗[ℚ] V)) :
    p1_realContract ω ((f.baseChange ℝ).dualMap φ) = g.baseChange ℝ (p1_realContract ω φ) := by
  obtain ⟨a, rfl⟩ := (p1l_e V).surjective φ
  rw [p1l_dualMap_baseChange_e, p1l_realContract_e, p1l_realContract_e, ← LinearMap.comp_apply,
    ← LinearMap.baseChange_comp, h, LinearMap.baseChange_comp, LinearMap.comp_apply]

/-- The functional `1 ⊗ φ₀` over `ℝ` is nonzero for `φ₀ ≠ 0`. -/
theorem p1l_e_one_tmul_ne_zero {φ₀ : Dual ℚ V} (h : φ₀ ≠ 0) : p1l_e V (1 ⊗ₜ φ₀) ≠ 0 := by
  intro h0
  apply h
  ext v
  have := LinearMap.congr_fun h0 (1 ⊗ₜ v)
  rw [p1l_e_tmul, one_mul, LinearMap.zero_apply] at this
  simpa using this

variable {ω : ⋀[ℚ]^2 V} {I : ℝ ⊗[ℚ] V →ₗ[ℝ] ℝ ⊗[ℚ] V}

/-- **Positivity implies nondegeneracy.** If `c φ₀ = 0` for `φ₀ ≠ 0`, then `φ = 1 ⊗ φ₀` has
`φ (c_ℝ (φ ∘ I)) = -(φ ∘ I) (c_ℝ φ) = 0`, against positivity. -/
theorem p1l_isNondegenerate_of_isPositive (h : p1_IsPositive ω I) : IsNondegenerate ω := by
  have hinj : Function.Injective (contract ω) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ₀ hφ₀
    by_contra hne
    have hc : p1_realContract ω (p1l_e V (1 ⊗ₜ φ₀)) = 0 := by
      rw [p1l_realContract_e, LinearMap.baseChange_tmul, hφ₀, TensorProduct.tmul_zero]
    have := h.2 _ (p1l_e_one_tmul_ne_zero hne)
    rw [p1l_realContract_skew, hc, map_zero, neg_zero] at this
    exact lt_irrefl _ this
  refine ⟨hinj, ?_⟩
  rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
  rw [Subspace.dual_finrank_eq]

omit [Module.Finite ℚ V] in
/-- `c ∘ fᵀ = f† ∘ c` for the adjoint `f† = p1_adjoint ω hω f`. -/
theorem p1l_contract_dualMap_adjoint (hω : IsNondegenerate ω) (f : Module.End ℚ V) :
    contract ω ∘ₗ f.dualMap = p1_adjoint ω hω f ∘ₗ contract ω := by
  ext φ
  simp [p1_adjoint]

/-- The real form `S (α, β) = β (c_ℝ (α ∘ I))` on `(ℝ ⊗ V)^∨`; for a positive `ω` and `I² = -1`
it is symmetric and positive definite.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §4.1 (the positive definite form
`E (i x, y)` of a polarization); Mumford, *Abelian Varieties*, §21. -/
def p1l_S (ω : ⋀[ℚ]^2 V) (I : ℝ ⊗[ℚ] V →ₗ[ℝ] ℝ ⊗[ℚ] V) :
    LinearMap.BilinForm ℝ (Dual ℝ (ℝ ⊗[ℚ] V)) :=
  LinearMap.mk₂ ℝ (fun α β => β (p1_realContract ω (α ∘ₗ I)))
    (fun _ _ _ => by simp [LinearMap.add_comp]) (fun _ _ _ => by simp [LinearMap.smul_comp])
    (fun _ _ _ => by simp) (fun _ _ _ => by simp)

/-- For `ω = 0` the form `S` is zero. -/
example (I : ℝ ⊗[ℚ] V →ₗ[ℝ] ℝ ⊗[ℚ] V) : p1l_S (0 : ⋀[ℚ]^2 V) I = 0 := by
  ext α β
  simp [p1l_S, p1_realContract]

theorem p1l_S_apply (α β : Dual ℝ (ℝ ⊗[ℚ] V)) :
    p1l_S ω I α β = β (p1_realContract ω (α ∘ₗ I)) :=
  rfl

/-- For a positive `ω` and `I² = -1`, the form `S` is symmetric. -/
theorem p1l_S_isSymm (h : p1_IsPositive ω I) (hI : I ∘ₗ I = -LinearMap.id) :
    (p1l_S ω I).IsSymm := by
  refine LinearMap.BilinForm.isSymm_def.2 fun α β => ?_
  rw [p1l_S_apply, p1l_S_apply, p1l_realContract_skew ω (β ∘ₗ I) α]
  have h1 := h.1 (α ∘ₗ I) β
  rw [LinearMap.comp_assoc, hI, LinearMap.comp_neg, LinearMap.comp_id, map_neg,
    LinearMap.comp_apply, map_neg, map_neg] at h1
  rw [← h1, LinearMap.comp_apply]

/-- **Positivity of `tr (f f†)`.** -/
theorem p1l_trace_pos (h : p1_IsPositive ω I) (hI : I ∘ₗ I = -LinearMap.id)
    {f : Module.End ℚ V} (hf : f.baseChange ℝ ∘ₗ I = I ∘ₗ f.baseChange ℝ) (hf0 : f ≠ 0)
    (hω : IsNondegenerate ω) :
    0 < LinearMap.trace ℚ V (f ∘ₗ p1_adjoint ω hω f) := by
  set g := p1_adjoint ω hω f
  have hK : ∀ x y, p1l_S ω I ((f.baseChange ℝ).dualMap x) y =
      p1l_S ω I x ((g.baseChange ℝ).dualMap y) := by
    intro x y
    rw [p1l_S_apply, p1l_S_apply, LinearMap.dualMap_apply', LinearMap.dualMap_apply',
      LinearMap.comp_assoc, hf, ← LinearMap.comp_assoc, ← LinearMap.dualMap_apply',
      p1l_realContract_dualMap ω (p1l_contract_dualMap_adjoint hω f), LinearMap.comp_apply]
  have hK0 : (f.baseChange ℝ).dualMap ≠ 0 := by
    intro h0
    apply hf0
    ext v : 1
    refine (Module.forall_dual_apply_eq_zero_iff ℚ (f v)).1 fun φ₀ => ?_
    have := LinearMap.congr_fun (LinearMap.congr_fun h0 (p1l_e V (1 ⊗ₜ φ₀))) (1 ⊗ₜ v)
    rw [p1l_dualMap_baseChange_e, LinearMap.baseChange_tmul, p1l_e_tmul, one_mul,
      LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.dualMap_apply] at this
    simpa using this
  have hpos := p1l_trace_pos_of_adjoint (p1l_S_isSymm h hI) (fun α hα => h.2 α hα) hK hK0
  rw [LinearMap.dualMap_comp_dualMap, ← LinearMap.baseChange_comp] at hpos
  have htr : LinearMap.trace ℝ _ ((f ∘ₗ g).baseChange ℝ).dualMap =
      LinearMap.trace ℝ _ ((f ∘ₗ g).baseChange ℝ) :=
    LinearMap.trace_transpose' _
  rw [htr, LinearMap.trace_baseChange, eq_ratCast] at hpos
  exact_mod_cast hpos

/-- The real contraction of a decomposable 2-vector:
`c_ℝ (u ∧ v) φ = φ (1 ⊗ u) • (1 ⊗ v) - φ (1 ⊗ v) • (1 ⊗ u)`. -/
theorem p1l_realContract_ιMulti (u v : V) (φ : Dual ℝ (ℝ ⊗[ℚ] V)) :
    p1_realContract (exteriorPower.ιMulti ℚ 2 ![u, v]) φ =
      φ (1 ⊗ₜ u) • ((1 : ℝ) ⊗ₜ[ℚ] v) - φ (1 ⊗ₜ v) • ((1 : ℝ) ⊗ₜ[ℚ] u) := by
  obtain ⟨a, rfl⟩ := (p1l_e V).surjective φ
  induction a using TensorProduct.inductionOn with
  | tmul r φ₀ =>
    rw [p1l_realContract_e, LinearMap.baseChange_tmul, contract_ιMulti, p1l_e_tmul, p1l_e_tmul]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, TensorProduct.tmul_sub,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.tmul_smul]
    simp [Algebra.smul_def, mul_comm]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, add_smul, hx, hy]
    abel

theorem p1l_realContract_sub (ω₁ ω₂ : ⋀[ℚ]^2 V) :
    p1_realContract (ω₁ - ω₂) = p1_realContract ω₁ - p1_realContract ω₂ := by
  simp [p1_realContract, LinearMap.baseChange_sub, LinearMap.sub_comp]

theorem p1l_realContract_neg (ω : ⋀[ℚ]^2 V) :
    p1_realContract (-ω) = -p1_realContract ω := by
  simp [p1_realContract, LinearMap.baseChange_neg, LinearMap.neg_comp]

omit [Module.Finite ℚ V] in
/-- The adjoint is characterized by `c ∘ fᵀ = f† ∘ c`. -/
theorem p1l_adjoint_eq (hω : IsNondegenerate ω) {f g : Module.End ℚ V}
    (h : contract ω ∘ₗ f.dualMap = g ∘ₗ contract ω) : p1_adjoint ω hω f = g := by
  ext x
  obtain ⟨φ, rfl⟩ := hω.2 x
  simpa [p1_adjoint] using LinearMap.congr_fun h φ

/-- The real dual form on contracted functionals: `E_ℝ (c_ℝ α, c_ℝ β) = β (c_ℝ α)`. -/
theorem p1l_dualForm_realContract (hω : IsNondegenerate ω) (α β : Dual ℝ (ℝ ⊗[ℚ] V)) :
    (dualForm hω).baseChange ℝ (p1_realContract ω α) (p1_realContract ω β) =
      β (p1_realContract ω α) := by
  obtain ⟨a, rfl⟩ := (p1l_e V).surjective α
  obtain ⟨b, rfl⟩ := (p1l_e V).surjective β
  induction a using TensorProduct.inductionOn with
  | tmul r φ₀ =>
    induction b using TensorProduct.inductionOn with
    | tmul s ψ₀ =>
      rw [p1l_e_realContract_tmul, p1l_realContract_e, p1l_realContract_e,
        LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        LinearMap.BilinForm.baseChange_tmul, dualForm_contract_contract, Algebra.smul_def]
      ring
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

theorem p1l_realContract_surjective (hω : IsNondegenerate ω) :
    Function.Surjective (p1_realContract ω) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r v =>
    obtain ⟨φ₀, rfl⟩ := hω.2 v
    exact ⟨p1l_e V (r ⊗ₜ φ₀), by rw [p1l_realContract_e, LinearMap.baseChange_tmul]⟩
  | add x y hx hy =>
    obtain ⟨α, rfl⟩ := hx
    obtain ⟨β, rfl⟩ := hy
    exact ⟨α + β, map_add _ _ _⟩

/-- Every real functional is `E_ℝ`-dual to its contraction: `α x = E_ℝ (x, c_ℝ α)`. -/
theorem p1l_apply_eq_dualForm (hω : IsNondegenerate ω) (α : Dual ℝ (ℝ ⊗[ℚ] V))
    (x : ℝ ⊗[ℚ] V) : α x = (dualForm hω).baseChange ℝ x (p1_realContract ω α) := by
  obtain ⟨β, rfl⟩ := p1l_realContract_surjective hω x
  rw [p1l_dualForm_realContract]

theorem p1l_dualForm_real_skew (hω : IsNondegenerate ω) (x y : ℝ ⊗[ℚ] V) :
    (dualForm hω).baseChange ℝ x y = -(dualForm hω).baseChange ℝ y x := by
  obtain ⟨α, rfl⟩ := p1l_realContract_surjective hω x
  obtain ⟨β, rfl⟩ := p1l_realContract_surjective hω y
  rw [p1l_dualForm_realContract, p1l_dualForm_realContract, p1l_realContract_skew]

theorem p1l_realContract_injective (hω : IsNondegenerate ω) :
    Function.Injective (p1_realContract ω) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro α hα
  refine LinearMap.ext fun x => ?_
  rw [p1l_apply_eq_dualForm hω, hα, map_zero, LinearMap.zero_apply]

/-- **Positivity through the dual form.** For nondegenerate `ω` and `I² = -1`, `p1_IsPositive ω I`
says that `E_ℝ` is `I`-invariant and `E_ℝ (x, I x) > 0` for `x ≠ 0`. -/
theorem p1l_isPositive_iff (hω : IsNondegenerate ω) (hI : ∀ x, I (I x) = -x) :
    p1_IsPositive ω I ↔
      (∀ x y, (dualForm hω).baseChange ℝ (I x) (I y) = (dualForm hω).baseChange ℝ x y) ∧
        ∀ x, x ≠ 0 → 0 < (dualForm hω).baseChange ℝ x (I x) := by
  set E := (dualForm hω).baseChange ℝ
  set c := p1_realContract ω
  -- `c (φ ∘ I) = -I (c φ)` under either side.
  have hR1 : (∀ φ ψ : Dual ℝ (ℝ ⊗[ℚ] V), (ψ ∘ₗ I) (c (φ ∘ₗ I)) = ψ (c φ)) →
      ∀ φ, c (φ ∘ₗ I) = -I (c φ) := by
    intro h1 φ
    refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℝ _).1 fun β => ?_)
    have h := h1 (φ ∘ₗ I) β
    have hφ : φ ∘ₗ I ∘ₗ I = -φ := by ext x; simp [hI]
    rw [LinearMap.comp_assoc, hφ, map_neg, LinearMap.comp_apply, map_neg, map_neg] at h
    rw [map_sub, ← h, map_neg, sub_neg_eq_add, neg_add_cancel]
  have hR2 : (∀ x y, E (I x) (I y) = E x y) → ∀ φ, c (φ ∘ₗ I) = -I (c φ) := by
    intro hinv φ
    obtain ⟨β, hβ⟩ := p1l_realContract_surjective hω (-I (c φ))
    rw [← hβ]
    congr 1
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, p1l_apply_eq_dualForm hω φ (I x), p1l_apply_eq_dualForm hω β x, hβ,
      map_neg, ← hinv x (I (c φ)), hI, map_neg, neg_neg]
  constructor
  · rintro ⟨h1, h2⟩
    have hR := hR1 h1
    have hRI : ∀ α, I (c α) = c (-(α ∘ₗ I)) := fun α => by rw [map_neg, hR, neg_neg]
    refine ⟨fun x y => ?_, fun x hx => ?_⟩
    · obtain ⟨α, rfl⟩ := p1l_realContract_surjective hω x
      obtain ⟨β, rfl⟩ := p1l_realContract_surjective hω y
      rw [hRI, hRI, p1l_dualForm_realContract, p1l_dualForm_realContract]
      simp only [map_neg, LinearMap.neg_apply, neg_neg]
      exact h1 α β
    · obtain ⟨α, rfl⟩ := p1l_realContract_surjective hω x
      have hα : α ≠ 0 := by rintro rfl; exact hx (map_zero _)
      have := h2 α hα
      rw [p1l_realContract_skew] at this
      rw [hRI, p1l_dualForm_realContract, LinearMap.neg_apply]
      exact this
  · rintro ⟨hinv, hpos⟩
    have hR := hR2 hinv
    refine ⟨fun φ ψ => ?_, fun φ hφ => ?_⟩
    · rw [LinearMap.comp_apply, hR, map_neg, hI, neg_neg]
    · rw [hR, map_neg, p1l_apply_eq_dualForm hω φ, p1l_dualForm_real_skew, neg_neg]
      exact hpos _ fun h0 => hφ (p1l_realContract_injective hω (by rw [h0, map_zero]))

end Real

end HodgeLean.Foundations
