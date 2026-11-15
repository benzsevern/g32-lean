import HodgeLean.Foundations.Program.CurveJacobianFormsLattice

/-!
# Track B3 foundations (stages B3.4b, B3.4d): finite dimensionality of `H¹_dR`

* `b3Forms_deRham_finiteDimensional`: on a compact connected manifold `H¹_dR(M)` is
  finite-dimensional. The periods of all closed forms along loops are integer combinations of
  finitely many transition values (`b3Forms_periods_mem_closure`), which are linear in the form;
  a closed form on which they all vanish has vanishing periods, hence is exact
  (`b3Forms_exists_primitive`).
* `b3Forms_reClass_injective`: on a compact connected Riemann surface `θ ↦ [Re θ]` is an injective
  real-linear map `Ω¹(C) → H¹_dR(C)` (Stokes' theorem and the Riemann positivity), so `Ω¹(C)` is
  finite-dimensional (`b3Forms_holForm_finiteDimensional`, the content of statement 1 of
  `CurveJacobian.lean`) and `2 dim_ℂ Ω¹(C) ≤ dim_ℝ H¹_dR(C)`;
* periods are `ℂ`-linear (`b3Forms_period_mem_linearDual`, the content of statement 3), and
  `rk Λ_C ≥ 2 dim_ℂ Ω¹(C)` (`b3Forms_two_mul_finrank_le_finrank_periodLattice`, one inequality of
  statement 6), and the periods span the dual of `Ω¹(C)` (`b3Forms_range_cplxPeriod`, the content
  of statement 8). -/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem b3Forms_ballPrim_add {α β : M → E [⋀^Fin 1]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α)
    (hβ : b3Forms_IsSmooth β) {x q : M} (hq : q ∈ b3Forms_cball E 2 x) :
    b3Forms_ballPrim (α + β) x q = b3Forms_ballPrim α x q + b3Forms_ballPrim β x q :=
  b3Forms_lineIntegral_add hα hβ (b3Forms_segPath_isTame x (convex_ball _ _)
    (b3Forms_ball_rad_subset x) (Metric.mem_ball_self (by linarith [b3Forms_rad_pos (E := E) x]))
    hq.2).1 0 1

theorem b3Forms_ballPrim_smul (c : ℝ) (α : M → E [⋀^Fin 1]→L[ℝ] ℝ) (x q : M) :
    b3Forms_ballPrim (c • α) x q = c * b3Forms_ballPrim α x q :=
  b3Forms_lineIntegral_smul c α _ 0 1

variable [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- **`H¹_dR` of a compact connected manifold is finite-dimensional.** -/
theorem b3Forms_deRham_finiteDimensional : FiniteDimensional ℝ (b3Forms_deRham E M 0) := by
  classical
  have : ProperSpace E := FiniteDimensional.proper_real E
  set Θ := b3Forms_closed E M 0
  set A : Θ → M → E [⋀^Fin 1]→L[ℝ] ℝ := fun α ↦ α.1.1
  obtain ⟨S, hS, hSf, hmem⟩ := b3Forms_periods_mem_closure (A := A) (fun α ↦ α.1.2)
    fun α ↦ b3Forms_closed_d_eq_zero α
  have : Fintype S := hS.fintype
  have hlin : ∀ s ∈ S, ∀ (c : ℝ) (α β : Θ), s (c • α + β) = c * s α + s β := by
    intro s hs c α β
    obtain ⟨x, y, q, hq, rfl⟩ := hSf s hs
    have hx := b3Forms_kball_subset_cball_two x hq.1
    have hy := b3Forms_kball_subset_cball_two y hq.2
    simp only [b3Forms_transVal, A, Submodule.coe_add, Submodule.coe_smul]
    have hca : b3Forms_IsSmooth (c • α.1.1) := α.1.2.smul c
    rw [b3Forms_ballPrim_add hca β.1.2 hx, b3Forms_ballPrim_add hca β.1.2 hy,
      b3Forms_ballPrim_smul, b3Forms_ballPrim_smul]
    ring
  let Φ : Θ →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun α s ↦ s.1 α
      map_add' := fun α β ↦ by
        funext s
        simpa using hlin s.1 s.2 1 α β
      map_smul' := fun c α ↦ by
        funext s
        have h := hlin s.1 s.2 c α 0
        have h0 := hlin s.1 s.2 1 0 0
        rw [one_smul, add_zero, one_mul] at h0
        have h00 : s.1 0 = 0 := by linarith
        rw [add_zero, h00, add_zero] at h
        simpa using h }
  set p := (b3Forms_exact E M 0).comap (b3Forms_closed E M 0).subtype
  have hker : LinearMap.ker Φ ≤ p := by
    intro α hα
    have h0 : ∀ s ∈ S, s α = 0 := fun s hs ↦ congrFun (LinearMap.mem_ker.1 hα) ⟨s, hs⟩
    have hev : ∀ f ∈ AddSubgroup.closure S, f α = 0 := fun f hf ↦ by
      induction hf using AddSubgroup.closure_induction with
      | mem f hf => exact h0 f hf
      | zero => rfl
      | add f g _ _ hf hg => simp [hf, hg]
      | neg f _ hf => simp [hf]
    have hper : b3Forms_PeriodsVanish α.1.1 := fun γ hp hγ ↦ hev _ (hmem γ hp hγ)
    obtain ⟨g, hg, hgα⟩ := b3Forms_exists_primitive α.1.2 (b3Forms_closed_d_eq_zero α) hper
    exact ⟨⟨b3Forms_fun g, hg⟩, Subtype.ext hgα⟩
  have : FiniteDimensional ℝ (Θ ⧸ LinearMap.ker Φ) :=
    Module.Finite.equiv Φ.quotKerEquivRange.symm
  exact Module.Finite.of_surjective (Submodule.factor hker) fun y ↦ by
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    exact ⟨Submodule.mkQ _ x, rfl⟩

end Real

section Hol

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

attribute [local instance] b3Forms_isManifold_real

theorem b3Forms_reForm_add (θ θ' : b3_HolForm E C) :
    b3Forms_reForm (θ + θ') = b3Forms_reForm θ + b3Forms_reForm θ' := by
  funext z
  ext v
  have : v = fun _ ↦ v 0 := funext fun i ↦ by fin_cases i; rfl
  rw [this, Pi.add_apply, ContinuousAlternatingMap.add_apply, b3Forms_reForm_apply,
    b3Forms_reForm_apply, b3Forms_reForm_apply]
  simp

theorem b3Forms_reForm_smul (c : ℝ) (θ : b3_HolForm E C) :
    b3Forms_reForm (c • θ) = c • b3Forms_reForm θ := by
  funext z
  ext v
  have : v = fun _ ↦ v 0 := funext fun i ↦ by fin_cases i; rfl
  rw [this, Pi.smul_apply, ContinuousAlternatingMap.smul_apply, b3Forms_reForm_apply,
    b3Forms_reForm_apply]
  simp [Submodule.coe_smul_of_tower]

variable (hE : Module.finrank ℂ E = 1)
include hE

/-- The real part of a holomorphic form as a closed real `1`-form.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §9 (holomorphic 1-forms) and §19 (harmonic
forms and H¹). -/
def b3Forms_reClosed : b3_HolForm E C →ₗ[ℝ] b3Forms_closed E C 0 where
  toFun θ := ⟨⟨b3Forms_reForm θ, b3Forms_isSmooth_reForm θ⟩,
    LinearMap.mem_ker.2 (Subtype.ext (b3Forms_d_reForm hE θ))⟩
  map_add' θ θ' := Subtype.ext (Subtype.ext (b3Forms_reForm_add θ θ'))
  map_smul' c θ := Subtype.ext (Subtype.ext (b3Forms_reForm_smul c θ))

/-- **The de Rham class of the real part**, `Ω¹(C) → H¹_dR(C)`, `θ ↦ [Re θ]`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §9 (holomorphic 1-forms) and §19 (harmonic
forms and H¹). -/
def b3Forms_reClass : b3_HolForm E C →ₗ[ℝ] b3Forms_deRham E C 0 :=
  (Submodule.mkQ _).comp (b3Forms_reClosed hE)

/-- **`θ ↦ [Re θ]` is injective** on a compact Riemann surface. -/
theorem b3Forms_reClass_injective [T2Space C] [CompactSpace C] :
    Function.Injective (b3Forms_reClass (C := C) hE) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro θ hθ
  have h := (Submodule.Quotient.mk_eq_zero _).1 hθ
  obtain ⟨γ, hγ⟩ := h
  have hγ' : b3Forms_d (b3Forms_fun (E := E) (b3Forms_toFun γ.1)) = b3Forms_reForm θ := by
    rw [b3Forms_fun_toFun]
    exact congrArg Subtype.val hγ
  have hs : b3Forms_IsSmooth (b3Forms_fun (E := E) (b3Forms_toFun γ.1)) := by
    rw [b3Forms_fun_toFun]; exact γ.2
  exact b3Forms_hol_eq_zero_of_reForm_exact hE θ hs hγ'

variable [T2Space C] [CompactSpace C] [ConnectedSpace C]

theorem b3Forms_holForm_finiteDimensional_real : FiniteDimensional ℝ (b3_HolForm E C) := by
  have := b3Forms_deRham_finiteDimensional (E := E) (M := C)
  exact FiniteDimensional.of_injective (b3Forms_reClass hE) (b3Forms_reClass_injective hE)

/-- **`Ω¹(C)` is finite-dimensional** for a compact connected Riemann surface (the content of
statement 1 of `CurveJacobian.lean`). -/
theorem b3Forms_holForm_finiteDimensional : FiniteDimensional ℂ (b3_HolForm E C) := by
  have := b3Forms_holForm_finiteDimensional_real (C := C) hE
  exact Module.Finite.of_restrictScalars_finite ℝ ℂ _

/-- **`2 dim_ℂ Ω¹(C) ≤ dim_ℝ H¹_dR(C)`.** -/
theorem b3Forms_two_mul_finrank_holForm_le :
    2 * Module.finrank ℂ (b3_HolForm E C) ≤ Module.finrank ℝ (b3Forms_deRham E C 0) := by
  have := b3Forms_deRham_finiteDimensional (E := E) (M := C)
  rw [← finrank_real_of_complex]
  exact LinearMap.finrank_le_finrank_of_injective (b3Forms_reClass_injective hE)

end Hol

end HodgeLean.Foundations.Program

namespace HodgeLean.Foundations.Program

section Rank

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

attribute [local instance] b3Forms_isManifold_real

theorem b3Forms_continuous_holIntegrand (θ : b3_HolForm E C) {γ : ℝ → C}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) :
    Continuous fun t ↦ θ.1 ⟨γ t, b3_velocity E C γ t⟩ := by
  have h : (fun t ↦ θ.1 ⟨γ t, b3_velocity E C γ t⟩) = fun t ↦
      ((b3Forms_reForm θ (γ t) (fun _ ↦ b3Forms_velocity γ t) : ℝ) : ℂ) +
        Complex.I * ((b3Forms_imForm θ (γ t) (fun _ ↦ b3Forms_velocity γ t) : ℝ) : ℂ) := by
    funext t
    rw [b3Forms_reForm_apply, b3Forms_imForm_apply, b3Forms_velocity_eq_b3, mul_comm]
    exact (Complex.re_add_im _).symm
  rw [h]
  exact (Complex.continuous_ofReal.comp
    (b3Forms_continuous_lineIntegrand (b3Forms_isSmooth_reForm θ) hγ)).add
    (continuous_const.mul (Complex.continuous_ofReal.comp
      (b3Forms_continuous_lineIntegrand (b3Forms_isSmooth_imForm θ) hγ)))

/-- **Periods are `ℂ`-linear** on holomorphic forms (the content of statement 3). -/
theorem b3Forms_period_mem_linearDual (γ : b3_SmoothLoop E C) :
    b3_period E C γ ∈ b3_linearDual E C := by
  intro a θ η
  simp only [b3_period, b3_pathPeriod, b3_pathIntegral, Submodule.coe_add,
    Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : IntervalIntegrable (fun t ↦ a * θ.1 ⟨γ.1 t, b3_velocity E C γ.1 t⟩) volume 0 1 :=
    (continuous_const.mul (b3Forms_continuous_holIntegrand θ γ.2.2)).intervalIntegrable 0 1
  have h2 : IntervalIntegrable (fun t ↦ η.1 ⟨γ.1 t, b3_velocity E C γ.1 t⟩) volume 0 1 :=
    (b3Forms_continuous_holIntegrand η γ.2.2).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul]

theorem b3Forms_periodLattice_le_linearDual :
    b3_periodLattice E C ≤ (b3_linearDual E C).toAddSubgroup := by
  rw [b3_periodLattice, AddSubgroup.closure_le]
  rintro _ ⟨γ, rfl⟩
  exact b3Forms_period_mem_linearDual γ

theorem b3Forms_linearDual_apply_zero {u : b3_HolForm E C → ℂ} (hu : u ∈ b3_linearDual E C) :
    u 0 = 0 := by
  have h := hu 1 0 0
  simp only [smul_zero, add_zero, one_mul] at h
  linear_combination -h

variable [T2Space C] [CompactSpace C] [ConnectedSpace C] (hE : Module.finrank ℂ E = 1)
include hE

/-- **`rk Λ_C ≥ 2 dim Ω¹(C)`**: the real parts of the periods separate holomorphic forms, so
`θ ↦ (λ ↦ Re λ(θ))` embeds `Ω¹(C)` (a real space of dimension `2 dim_ℂ Ω¹`) into
`Hom_ℤ(Λ_C, ℝ)`, of dimension `rk Λ_C`. -/
theorem b3Forms_two_mul_finrank_le_finrank_periodLattice :
    2 * Module.finrank ℂ (b3_HolForm E C) ≤ Module.finrank ℤ (b3_periodLattice E C) := by
  have : Module.Finite ℤ (b3_periodLattice E C) := b3Forms_periodLattice_finite hE
  have : FiniteDimensional ℂ (b3_HolForm E C) := b3Forms_holForm_finiteDimensional hE
  set Λ := b3_periodLattice E C
  have hlin : ∀ l : Λ, l.1 ∈ b3_linearDual E C := fun l ↦ b3Forms_periodLattice_le_linearDual l.2
  let Ψ : b3_HolForm E C →ₗ[ℝ] (Λ →ₗ[ℤ] ℝ) :=
    { toFun := fun θ ↦
        { toFun := fun l ↦ (l.1 θ).re
          map_add' := fun l l' ↦ by simp
          map_smul' := fun n l ↦ by simp }
      map_add' := fun θ θ' ↦ by
        ext l
        have h := hlin l 1 θ θ'
        simp only [one_smul, one_mul] at h
        simp [h]
      map_smul' := fun c θ ↦ by
        ext l
        have h := hlin l (c : ℂ) θ 0
        rw [add_zero, b3Forms_linearDual_apply_zero (hlin l), add_zero] at h
        simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply,
          smul_eq_mul]
        rw [show c • θ = (c : ℂ) • θ from (Complex.coe_smul c θ).symm, h]
        simp }
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro θ hθ
    have hper : b3Forms_PeriodsVanish (b3Forms_reForm θ) := fun γ hp hγ ↦ by
      have h1 := LinearMap.congr_fun hθ (b3_latticePeriod E C ⟨γ, hp, hγ⟩)
      have h2 := congrArg Complex.re (b3Forms_period_eq θ ⟨γ, hp, hγ⟩)
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply, Ψ] at h1
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, zero_mul, one_mul, mul_zero, sub_zero, add_zero] at h2
      rw [← h2]
      exact h1
    obtain ⟨g, hg, hdg⟩ := b3Forms_exists_primitive (b3Forms_isSmooth_reForm θ)
      (b3Forms_d_reForm hE θ) hper
    exact b3Forms_hol_eq_zero_of_reForm_exact hE θ hg hdg
  set b := Module.Free.chooseBasis ℤ Λ
  have e : (Λ →ₗ[ℤ] ℝ) ≃ₗ[ℝ] (Module.Free.ChooseBasisIndex ℤ Λ → ℝ) := (b.constr ℝ).symm
  have : FiniteDimensional ℝ (Λ →ₗ[ℤ] ℝ) := Module.Finite.equiv e.symm
  calc 2 * Module.finrank ℂ (b3_HolForm E C) = Module.finrank ℝ (b3_HolForm E C) :=
        (finrank_real_of_complex _).symm
    _ ≤ Module.finrank ℝ (Λ →ₗ[ℤ] ℝ) := LinearMap.finrank_le_finrank_of_injective hinj
    _ = Module.finrank ℤ Λ := by
        rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card,
          Module.finrank_eq_card_chooseBasisIndex]

/-- **The periods span the dual of `Ω¹(C)`** (the content of statement 8 of
`CurveJacobian.lean`): the range of the complexified period map is the space of linear
functionals. -/
theorem b3Forms_range_cplxPeriod :
    LinearMap.range (b3_cplxPeriod E C) = b3_linearDual E C := by
  have : FiniteDimensional ℂ (b3_HolForm E C) := b3Forms_holForm_finiteDimensional hE
  have hlin : ∀ l : b3_periodLattice E C, l.1 ∈ b3_linearDual E C := fun l ↦
    b3Forms_periodLattice_le_linearDual l.2
  rw [b3_cplxPeriod, LinearMap.range_liftBaseChange]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    exact hlin l
  · intro u hu
    let φ : Module.Dual ℂ (b3_HolForm E C) →ₗ[ℂ] (b3_HolForm E C → ℂ) :=
      { toFun := fun f ↦ ⇑f, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
    let W : Submodule ℂ (Module.Dual ℂ (b3_HolForm E C)) :=
      (Submodule.span ℂ (LinearMap.range
        (b3_periodLattice E C).subtype.toIntLinearMap : Set (b3_HolForm E C → ℂ))).comap φ
    let toDual : ∀ v : b3_HolForm E C → ℂ, v ∈ b3_linearDual E C →
        Module.Dual ℂ (b3_HolForm E C) := fun v hv ↦
      { toFun := v
        map_add' := fun θ θ' ↦ by simpa using hv 1 θ θ'
        map_smul' := fun a θ ↦ by simpa [b3Forms_linearDual_apply_zero hv] using hv a θ 0 }
    have hW : W.dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro θ hθ
      rw [Submodule.mem_bot]
      refine b3Forms_hol_eq_zero_of_periods hE θ fun γ ↦ ?_
      have hf : toDual _ (hlin (b3_latticePeriod E C γ)) ∈ W :=
        Submodule.subset_span ⟨b3_latticePeriod E C γ, rfl⟩
      exact (Submodule.mem_dualCoannihilator θ).1 hθ _ hf
    have hWt : W = ⊤ := by
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hW,
        Submodule.dualAnnihilator_bot]
    have : toDual u hu ∈ W := hWt ▸ Submodule.mem_top
    exact this

end Rank

end HodgeLean.Foundations.Program
