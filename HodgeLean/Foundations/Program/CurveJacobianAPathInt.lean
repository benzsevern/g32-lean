import HodgeLean.Foundations.Program.CurveJacobianAPaths

/-! # Track B3, lane A: integrals of holomorphic forms along good paths

Change of variables, reversal and concatenation of path integrals, the loop of a closed good path,
and the good reparametrization of a `C¹` path.
-/

noncomputable section

open Manifold Filter Topology Set
open scoped ContDiff

namespace HodgeLean.Foundations.Program

section PathInt

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C]

/-- The integrand `t ↦ θ(γ t, γ' t)`. -/
def b3A_integrand (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (γ : ℝ → C) (t : ℝ) : ℂ :=
  θ ⟨γ t, b3_velocity E C γ t⟩

/-- Locally equal paths have equal integrands. -/
theorem b3A_integrand_congr (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) {γ₁ γ₂ : ℝ → C} {t : ℝ}
    (h : γ₁ =ᶠ[𝓝 t] γ₂) : b3A_integrand θ γ₁ t = b3A_integrand θ γ₂ t := by
  have hp : γ₁ t = γ₂ t := h.eq_of_nhds
  have hv : b3A_vel (E := E) γ₁ t = b3A_vel (E := E) γ₂ t := by
    rw [b3A_vel, b3A_vel, b3_velocity, b3_velocity, h.mfderiv_eq]
    rfl
  show θ (Bundle.TotalSpace.mk' E (γ₁ t) (b3A_vel (E := E) γ₁ t)) =
    θ (Bundle.TotalSpace.mk' E (γ₂ t) (b3A_vel (E := E) γ₂ t))
  rw [hp, hv]

/-- The chain rule for a reparametrization, `(γ ∘ σ)' = σ' γ'(σ)`. -/
theorem b3A_velocity_reparam (γ : ℝ → C) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ)
    (σ : ℝ → ℝ) (hσ : Differentiable ℝ σ) (t : ℝ) :
    b3A_vel (E := E) (γ ∘ σ) t = ((deriv σ t : ℝ) : ℂ) • b3A_vel (E := E) γ (σ t) := by
  rw [Complex.coe_smul]
  have h1 : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) σ t := (hσ t).mdifferentiableAt
  have h2 := mfderiv_comp_apply t ((hγ (σ t)).mdifferentiableAt one_ne_zero) h1 1
  have h3 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) σ t 1 =
      deriv σ t • (1 : TangentSpace 𝓘(ℝ, ℝ) (σ t)) := by
    rw [mfderiv_eq_fderiv]
    simp only [NormedSpace.fromTangentSpace, tangentSpaceCastModel]
    change fderiv ℝ σ t 1 = deriv σ t * 1
    rw [mul_one]
    rfl
  rw [h3, map_smul] at h2
  exact h2

/-- A holomorphic form is homogeneous on each tangent space. -/
theorem b3A_holForm_smul_apply [IsManifold 𝓘(ℂ, E) ω C] {θ : TangentBundle 𝓘(ℂ, E) C → ℂ}
    (hθ : θ ∈ b3_HolForm E C) (x : C) (c : ℂ) (v : TangentSpace 𝓘(ℂ, E) x) :
    θ ⟨x, c • v⟩ = c * θ ⟨x, v⟩ := by
  have h := hθ.2 x c v 0
  have h0 := hθ.2 x 1 0 0
  simp only [add_zero, one_smul, one_mul] at h h0
  have hz : θ ⟨x, 0⟩ = 0 := by linear_combination -h0
  rw [hz, add_zero] at h
  exact h

/-- **Change of variables** for integrals of holomorphic forms along `C¹` paths. -/
theorem b3A_integral_reparam [IsManifold 𝓘(ℂ, E) ω C] {θ : TangentBundle 𝓘(ℂ, E) C → ℂ}
    (hθ : θ ∈ b3_HolForm E C) (γ : ℝ → C) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ)
    (σ : ℝ → ℝ) (hσ : ContDiff ℝ 1 σ) (a b : ℝ) :
    ∫ t in a..b, b3A_integrand θ (γ ∘ σ) t = ∫ s in σ a..σ b, b3A_integrand θ γ s := by
  have hd : Differentiable ℝ σ := hσ.differentiable one_ne_zero
  have hpt : ∀ t, b3A_integrand θ (γ ∘ σ) t = deriv σ t • b3A_integrand θ γ (σ t) := by
    intro t
    have hv := b3A_velocity_reparam γ hγ σ hd t
    show θ (Bundle.TotalSpace.mk' E (γ (σ t)) (b3A_vel (E := E) (γ ∘ σ) t)) = _
    rw [hv, Complex.real_smul]
    exact b3A_holForm_smul_apply hθ (γ (σ t)) _ (b3A_vel (E := E) γ (σ t))
  rw [intervalIntegral.integral_congr (fun t _ ↦ hpt t)]
  exact intervalIntegral.integral_deriv_smul_comp (fun t _ ↦ (hd t).hasDerivAt)
    (hσ.continuous_deriv le_rfl).continuousOn (b3A_continuous_integrand γ hγ ⟨θ, hθ⟩)

/-- Reversing a path negates the integral. -/
theorem b3A_pathIntegral_symm [IsManifold 𝓘(ℂ, E) ω C] {θ : TangentBundle 𝓘(ℂ, E) C → ℂ}
    (hθ : θ ∈ b3_HolForm E C) (γ : ℝ → C) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) :
    b3_pathIntegral E C (fun t ↦ γ (1 - t)) θ = -b3_pathIntegral E C γ θ := by
  have := b3A_integral_reparam hθ γ hγ (fun t ↦ 1 - t) (contDiff_const.sub contDiff_id) 0 1
  simp only [sub_zero, sub_self] at this
  rw [intervalIntegral.integral_symm (a := (0 : ℝ)) (b := 1)] at this
  exact this

/-- **Concatenation adds integrals.** -/
theorem b3A_pathIntegral_trans [IsManifold 𝓘(ℂ, E) ω C] {θ : TangentBundle 𝓘(ℂ, E) C → ℂ}
    (hθ : θ ∈ b3_HolForm E C) {γ δ : ℝ → C} {p q r : C} (hγ : b3A_IsGoodPath (E := E) γ p q)
    (hδ : b3A_IsGoodPath (E := E) δ q r) :
    b3_pathIntegral E C (fun t ↦ if t ≤ 1 / 2 then γ (2 * t) else δ (2 * t - 1)) θ =
      b3_pathIntegral E C γ θ + b3_pathIntegral E C δ θ := by
  set τ : ℝ → C := fun t ↦ if t ≤ 1 / 2 then γ (2 * t) else δ (2 * t - 1)
  have hτ := (hγ.trans hδ).1
  have hint : ∀ a b : ℝ, IntervalIntegrable (b3A_integrand θ τ) MeasureTheory.volume a b :=
    fun a b ↦ (b3A_continuous_integrand τ hτ ⟨θ, hθ⟩).intervalIntegrable a b
  have h2 : Continuous (fun t : ℝ ↦ 2 * t) := continuous_const.mul continuous_id
  have hq1 : ∀ᶠ t in 𝓝 (1 / 2 : ℝ), γ (2 * t) = q := by
    have : Tendsto (fun t : ℝ ↦ 2 * t) (𝓝 (1 / 2)) (𝓝 1) := by
      simpa using h2.tendsto (1 / 2 : ℝ)
    exact this.eventually hγ.2.2
  have hq2 : ∀ᶠ t in 𝓝 (1 / 2 : ℝ), δ (2 * t - 1) = q := by
    have : Tendsto (fun t : ℝ ↦ 2 * t - 1) (𝓝 (1 / 2)) (𝓝 0) := by
      have := ((continuous_const.mul continuous_id).sub continuous_const :
        Continuous fun t : ℝ ↦ 2 * t - 1).tendsto (1 / 2 : ℝ)
      norm_num at this
      exact this
    exact this.eventually hδ.2.1
  have hτq : ∀ᶠ t in 𝓝 (1 / 2 : ℝ), τ t = q := by
    filter_upwards [hq1, hq2] with t h1 h2
    simp only [τ]
    split_ifs <;> assumption
  have hleft : ∀ t ∈ uIcc (0 : ℝ) (1 / 2), b3A_integrand θ τ t =
      b3A_integrand θ (γ ∘ fun t ↦ 2 * t) t := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    refine b3A_integrand_congr θ ?_
    rcases ht.2.lt_or_eq with h | rfl
    · filter_upwards [Iio_mem_nhds h] with s hs
      exact ite_eq_left (le_of_lt hs)
    · filter_upwards [hτq, hq1] with s h1 h2
      exact h1.trans h2.symm
  have hright : ∀ t ∈ uIcc (1 / 2 : ℝ) 1, b3A_integrand θ τ t =
      b3A_integrand θ (δ ∘ fun t ↦ 2 * t - 1) t := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    refine b3A_integrand_congr θ ?_
    rcases ht.1.lt_or_eq with h | h
    · filter_upwards [Ioi_mem_nhds h] with s hs
      exact ite_eq_right (not_le.2 hs)
    · subst h
      filter_upwards [hτq, hq2] with s h1 h2
      exact h1.trans h2.symm
  show ∫ t in (0 : ℝ)..1, b3A_integrand θ τ t =
    (∫ t in (0 : ℝ)..1, b3A_integrand θ γ t) + ∫ t in (0 : ℝ)..1, b3A_integrand θ δ t
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 (1 / 2)) (hint (1 / 2) 1),
    intervalIntegral.integral_congr hleft, intervalIntegral.integral_congr hright,
    b3A_integral_reparam hθ γ hγ.1 (fun t ↦ 2 * t) (contDiff_const.mul contDiff_id),
    b3A_integral_reparam hθ δ hδ.1 (fun t ↦ 2 * t - 1)
      ((contDiff_const.mul contDiff_id).sub contDiff_const)]
  norm_num

/-- A closed good path, extended periodically, near every integer is constant. -/
theorem b3A_fract_eventually {γ : ℝ → C} {p : C} (hγ : b3A_IsGoodPath (E := E) γ p p) (n : ℤ) :
    ∀ᶠ t in 𝓝 (n : ℝ), γ (Int.fract t) = p := by
  have h0 : Tendsto (fun t : ℝ ↦ t - n) (𝓝 (n : ℝ)) (𝓝 0) := by
    simpa using (continuous_sub_right (n : ℝ)).tendsto (n : ℝ)
  have h1 : Tendsto (fun t : ℝ ↦ t - n + 1) (𝓝 (n : ℝ)) (𝓝 1) := by
    have hc : Continuous fun t : ℝ ↦ t - n + 1 := by fun_prop
    simpa using hc.tendsto (n : ℝ)
  filter_upwards [h0.eventually hγ.2.1, h1.eventually hγ.2.2,
    Ioo_mem_nhds (show (n : ℝ) - 1 < n by linarith) (show (n : ℝ) < n + 1 by linarith)]
    with t ha hb hI
  rcases lt_or_ge t n with h | h
  · have : Int.floor t = n - 1 := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith [hI.1]
    rw [Int.fract, this]
    push_cast
    convert hb using 2
    ring
  · have : Int.floor t = n := by
      rw [Int.floor_eq_iff]
      exact ⟨h, hI.2⟩
    rw [Int.fract, this]
    exact ha

/-- **The loop of a closed good path**, `t ↦ γ (fract t)`. -/
def b3A_toLoop {γ : ℝ → C} {p : C} (hγ : b3A_IsGoodPath (E := E) γ p p) : b3_SmoothLoop E C :=
  ⟨fun t ↦ γ (Int.fract t), fun t ↦ by simp [Int.fract_add_one], fun t₀ ↦ by
    by_cases h : Int.fract t₀ = 0
    · obtain ⟨n, hn⟩ : ∃ n : ℤ, t₀ = n := ⟨⌊t₀⌋, by
        have := Int.floor_add_fract t₀
        rw [h, add_zero] at this
        exact this.symm⟩
      subst hn
      exact (contMDiffAt_const (c := p)).congr_of_eventuallyEq (b3A_fract_eventually hγ n)
    · have hI : t₀ ∈ Ioo (⌊t₀⌋ : ℝ) (⌊t₀⌋ + 1) :=
        ⟨lt_of_le_of_ne (Int.floor_le t₀) fun h' ↦ h (by rw [Int.fract, ← h', Int.floor_intCast,
          sub_self]),
          Int.lt_floor_add_one t₀⟩
      refine (hγ.1.comp (contDiff_id.sub contDiff_const).contMDiff t₀ :
        ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (fun t ↦ γ (t - ⌊t₀⌋)) t₀).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hI.1 hI.2] with t ht
      have : Int.floor t = ⌊t₀⌋ := by
        rw [Int.floor_eq_iff]
        exact ⟨ht.1.le, ht.2⟩
      simp only [Int.fract, this, Function.comp_apply, id]⟩

/-- The loop of a closed good path has the same integral. -/
theorem b3A_toLoop_pathIntegral (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) {γ : ℝ → C} {p : C}
    (hγ : b3A_IsGoodPath (E := E) γ p p) :
    b3_pathIntegral E C (b3A_toLoop hγ).1 θ = b3_pathIntegral E C γ θ := by
  refine intervalIntegral.integral_congr fun t ht ↦ b3A_integrand_congr θ ?_
  rw [uIcc_of_le zero_le_one] at ht
  rcases ht.1.lt_or_eq with h0 | h0
  · rcases ht.2.lt_or_eq with h1 | h1
    · filter_upwards [Ioo_mem_nhds h0 h1] with s hs
      show γ (Int.fract s) = γ s
      rw [Int.fract_eq_self.2 ⟨hs.1.le, hs.2⟩]
    · subst h1
      have := b3A_fract_eventually hγ 1
      push_cast at this
      filter_upwards [this, hγ.2.2] with s h1 h2
      exact h1.trans h2.symm
  · subst h0
    have := b3A_fract_eventually hγ 0
    push_cast at this
    filter_upwards [this, hγ.2.1] with s h1 h2
    exact h1.trans h2.symm

/-- The smooth step `σ(t) = smoothTransition (3 t - 1)`. -/
def b3A_step (t : ℝ) : ℝ := Real.smoothTransition (3 * t - 1)

/-- The smooth step is `C¹`. -/
theorem b3A_step_contDiff : ContDiff ℝ 1 b3A_step :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

/-- Every `C¹` path reparametrizes to a good path. -/
theorem b3A_isGoodPath_reparam (γ : ℝ → C) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) :
    b3A_IsGoodPath (E := E) (γ ∘ b3A_step) (γ 0) (γ 1) := by
  refine ⟨hγ.comp b3A_step_contDiff.contMDiff, ?_, ?_⟩
  · filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 3 by norm_num)] with t ht
    have : b3A_step t = 0 := Real.smoothTransition.zero_of_nonpos (by
      have : t < 1 / 3 := ht
      linarith)
    simp [this]
  · filter_upwards [Ioi_mem_nhds (show (2 / 3 : ℝ) < 1 by norm_num)] with t ht
    have : b3A_step t = 1 := Real.smoothTransition.one_of_one_le (by
      have : 2 / 3 < t := ht
      linarith)
    simp [this]

/-- The good reparametrization has the same integral. -/
theorem b3A_pathIntegral_reparam [IsManifold 𝓘(ℂ, E) ω C] {θ : TangentBundle 𝓘(ℂ, E) C → ℂ}
    (hθ : θ ∈ b3_HolForm E C) (γ : ℝ → C) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) :
    b3_pathIntegral E C (γ ∘ b3A_step) θ = b3_pathIntegral E C γ θ := by
  have := b3A_integral_reparam hθ γ hγ b3A_step b3A_step_contDiff 0 1
  have h0 : b3A_step 0 = 0 := Real.smoothTransition.zero_of_nonpos (by norm_num)
  have h1 : b3A_step 1 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)
  rw [h0, h1] at this
  exact this

end PathInt

end HodgeLean.Foundations.Program
