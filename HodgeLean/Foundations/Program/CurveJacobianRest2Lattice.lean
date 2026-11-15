import HodgeLean.Foundations.Program.CurveJacobianRest2Closed

/-! # Track B3, lane Rest2: the wedge pairing on holomorphic forms and the period lattice

On a compact connected Riemann surface `C`:
* `b3Rest2_W θ φ = ∫ Re θ ∧ Re φ` is a real bilinear form on `Ω¹(C)`, skew, and nondegenerate
  since `W(θ, iθ) = -∫ Re θ ∧ Im θ < 0` (Riemann positivity);
* for a loop `γ` with a smooth dual form `η` (`∫ ω ∧ η = ∫_γ ω` for closed `ω`), `η` is closed
  (`CurveJacobianRest2Closed.lean`), so `η = Re θ_γ + dg` by the Hodge decomposition, and
  `W(φ, θ_γ) = Re ∫_γ φ`. Hence `θ_γ` depends only on the period of `γ`; for `λ` in the period
  lattice, `b3Rest2_θ λ` is the form with `W(φ, θ_λ) = Re λ(φ)`;
* `b3Rest2_Q λ μ = Re μ(θ_λ)`, a real biadditive form on the lattice, and
  `b3Rest2_Q λ_γ λ_δ = ∫_δ η_γ` for every dual form `η_γ` of `γ`.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Metric
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

attribute [local instance] b3Forms_isManifold_real

theorem b3Rest2_re_period (θ : b3_HolForm E C) (γ : b3_SmoothLoop E C) :
    (b3_period E C γ θ).re = b3Forms_lineIntegral (b3Forms_reForm θ) γ.1 0 1 := by
  rw [b3Forms_period_eq]
  simp

theorem b3Rest2_reForm_I (θ : b3_HolForm E C) :
    b3Forms_reForm (Complex.I • θ) = (-1 : ℝ) • b3Forms_imForm θ := by
  rw [b3Forms_imForm_eq, ← b3Forms_reForm_smul]
  congr 1
  rw [show ((-1 : ℝ) • ((-Complex.I) • θ)) = ((-1 : ℝ) : ℂ) • ((-Complex.I) • θ) from
    (Complex.coe_smul _ _).symm, smul_smul]
  congr 1
  push_cast
  ring

variable [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E]
variable (hE : Module.finrank ℂ E = 1)

/-- **The wedge pairing** `W(θ, φ) = ∫ Re θ ∧ Re φ` on holomorphic forms. -/
def b3Rest2_W : LinearMap.BilinForm ℝ (b3_HolForm E C) :=
  (b3Forms_deRhamPairing (b3Rest_b hE) b3Forms_oriented_complex).compl₁₂
    (b3Forms_reClass hE) (b3Forms_reClass hE)

theorem b3Rest2_W_apply (θ φ : b3_HolForm E C) :
    b3Rest2_W hE θ φ = b3Forms_integral (b3Rest_b hE)
      (b3Forms_wedgeForm (b3Forms_reForm θ) (b3Forms_reForm φ)) := rfl

theorem b3Rest2_W_skew (θ φ : b3_HolForm E C) : b3Rest2_W hE φ θ = -b3Rest2_W hE θ φ :=
  b3Forms_pairing_comm (b3Rest_b hE) _ _

theorem b3Rest2_W_I_neg {θ : b3_HolForm E C} (hθ : θ ≠ 0) :
    b3Rest2_W hE θ (Complex.I • θ) < 0 := by
  rw [b3Rest2_W_apply, b3Rest2_reForm_I, b3Rest_wedgeForm_smul, b3Forms_integral_smul]
  have := b3Forms_integral_reIm_pos hE (b3Rest_e_ne_zero hE) θ hθ
  linarith

theorem b3Rest2_W_nondegenerate : (b3Rest2_W (C := C) hE).Nondegenerate := by
  refine ⟨fun θ h ↦ ?_, fun θ h ↦ ?_⟩
  · by_contra hθ
    have := b3Rest2_W_I_neg hE hθ
    rw [h] at this
    exact lt_irrefl _ this
  · by_contra hθ
    have h1 := b3Rest2_W_I_neg hE hθ
    have h2 := h (Complex.I • θ)
    rw [b3Rest2_W_skew] at h2
    linarith

/-- The real part of a lattice vector, as a real linear functional on `Ω¹(C)`. -/
def b3Rest2_ρ : b3_periodLattice E C →+ Module.Dual ℝ (b3_HolForm E C) where
  toFun l :=
    { toFun := fun θ ↦ (l.1 θ).re
      map_add' := fun θ θ' ↦ by
        have h := b3Forms_periodLattice_le_linearDual l.2 1 θ θ'
        simp only [one_smul, one_mul] at h
        simp [h]
      map_smul' := fun c θ ↦ by
        have hl := b3Forms_periodLattice_le_linearDual l.2
        have h := hl (c : ℂ) θ 0
        rw [add_zero, b3Forms_linearDual_apply_zero hl, add_zero] at h
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [show c • θ = (c : ℂ) • θ from (Complex.coe_smul c θ).symm, h]
        simp }
  map_zero' := by ext θ; simp
  map_add' l l' := by ext θ; simp

theorem b3Rest2_ρ_apply (l : b3_periodLattice E C) (θ : b3_HolForm E C) :
    b3Rest2_ρ l θ = (l.1 θ).re := rfl

variable [ConnectedSpace C]

/-- **The form `θ_λ` of a lattice vector**: `W(φ, θ_λ) = Re λ(φ)` for all `φ`. -/
def b3Rest2_θ (l : b3_periodLattice E C) : b3_HolForm E C :=
  haveI := b3Forms_holForm_finiteDimensional_real (C := C) hE
  ((b3Rest2_W hE).flip.toDual (b3Rest2_W_nondegenerate hE).flip).symm (b3Rest2_ρ l)

theorem b3Rest2_W_θ (l : b3_periodLattice E C) (φ : b3_HolForm E C) :
    b3Rest2_W hE φ (b3Rest2_θ hE l) = (l.1 φ).re := by
  haveI := b3Forms_holForm_finiteDimensional_real (C := C) hE
  have := LinearMap.BilinForm.toDual_def (B := (b3Rest2_W hE).flip)
    (b3Rest2_W_nondegenerate hE).flip (m := b3Rest2_θ hE l) (n := φ)
  have h1 : b3Rest2_W hE φ (b3Rest2_θ hE l) = ((b3Rest2_W hE).flip.toDual
      (b3Rest2_W_nondegenerate hE).flip (b3Rest2_θ hE l)) φ := this.symm
  rw [h1]
  unfold b3Rest2_θ
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem b3Rest2_θ_unique (l : b3_periodLattice E C) {θ : b3_HolForm E C}
    (h : ∀ φ, b3Rest2_W hE φ θ = (l.1 φ).re) : θ = b3Rest2_θ hE l := by
  have h0 : ∀ φ, b3Rest2_W hE φ (θ - b3Rest2_θ hE l) = 0 := fun φ ↦ by
    rw [map_sub, h, b3Rest2_W_θ, sub_self]
  exact sub_eq_zero.1 ((b3Rest2_W_nondegenerate hE).2 _ h0)

theorem b3Rest2_θ_add (l l' : b3_periodLattice E C) :
    b3Rest2_θ hE (l + l') = b3Rest2_θ hE l + b3Rest2_θ hE l' := by
  refine (b3Rest2_θ_unique hE (l + l') fun φ ↦ ?_).symm
  rw [map_add, b3Rest2_W_θ, b3Rest2_W_θ]
  simp

/-- `θ` as an additive map. -/
def b3Rest2_θHom : b3_periodLattice E C →+ b3_HolForm E C where
  toFun := b3Rest2_θ hE
  map_zero' := by
    refine (b3Rest2_θ_unique hE 0 fun φ ↦ ?_).symm
    simp
  map_add' := b3Rest2_θ_add hE

/-- **The real intersection pairing** on the period lattice, `Q(λ, μ) = Re μ(θ_λ)`. -/
def b3Rest2_Q (l m : b3_periodLattice E C) : ℝ := (m.1 (b3Rest2_θ hE l)).re

theorem b3Rest2_Q_eq_W (l m : b3_periodLattice E C) :
    b3Rest2_Q hE l m = b3Rest2_W hE (b3Rest2_θ hE l) (b3Rest2_θ hE m) :=
  (b3Rest2_W_θ hE m _).symm

theorem b3Rest2_Q_add_left (l l' m : b3_periodLattice E C) :
    b3Rest2_Q hE (l + l') m = b3Rest2_Q hE l m + b3Rest2_Q hE l' m := by
  simp only [b3Rest2_Q_eq_W, b3Rest2_θ_add, map_add, LinearMap.add_apply]

theorem b3Rest2_Q_add_right (l m m' : b3_periodLattice E C) :
    b3Rest2_Q hE l (m + m') = b3Rest2_Q hE l m + b3Rest2_Q hE l m' := by
  simp only [b3Rest2_Q_eq_W, b3Rest2_θ_add, map_add]

theorem b3Rest2_Q_skew (l m : b3_periodLattice E C) :
    b3Rest2_Q hE m l = -b3Rest2_Q hE l m := by
  rw [b3Rest2_Q_eq_W, b3Rest2_Q_eq_W, b3Rest2_W_skew]

/-! ## The form of a loop -/

/-- **The Hodge part of a closed dual form computes `θ`**: if `η` is a dual form of `γ` and
`η = Re θ + dg`, then `θ = θ_{λ_γ}`. -/
theorem b3Rest2_θ_eq_of_dual (γ : b3_SmoothLoop E C) {η : C → E [⋀^Fin 1]→L[ℝ] ℝ}
    (hη : b3Forms_IsSmooth η)
    (hη' : ∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth α → b3Forms_d α = 0 →
      b3Forms_integral (b3Rest_b hE) (b3Forms_wedgeForm α η) = b3Forms_lineIntegral α γ.1 0 1)
    {θ : b3_HolForm E C} {g : C → ℝ} (hg : b3Forms_IsSmooth (b3Forms_fun (E := E) g))
    (heq : η = b3Forms_reForm θ + b3Forms_d (b3Forms_fun (E := E) g)) :
    θ = b3Rest2_θ hE (b3_latticePeriod E C γ) := by
  refine b3Rest2_θ_unique hE _ fun φ ↦ ?_
  have hφ := b3Forms_isSmooth_reForm φ
  have h1 := hη' _ hφ (b3Forms_d_reForm hE φ)
  rw [heq, b3Rest_wedgeForm_add, b3Forms_integral_add _ (hφ.wedgeForm (b3Forms_isSmooth_reForm θ))
    (hφ.wedgeForm hg.d)] at h1
  have h2 : b3Forms_integral (b3Rest_b hE) (b3Forms_wedgeForm (b3Forms_reForm φ)
      (b3Forms_d (b3Forms_fun (E := E) g))) = 0 := by
    have := b3Forms_integral_wedge_d_eq_zero (b3Rest_b hE) b3Forms_oriented_complex hg hφ
      (b3Forms_d_reForm hE φ)
    have hc := b3Forms_pairing_comm (b3Rest_b hE) (b3Forms_d (b3Forms_fun (E := E) g))
      (b3Forms_reForm φ)
    rw [this, neg_zero] at hc
    exact hc
  rw [h2, add_zero] at h1
  rw [b3Rest2_W_apply, h1]
  exact (b3Rest2_re_period φ γ).symm

/-- **Every loop has a closed dual form, and its Hodge part is `θ_{λ_γ}`.** -/
theorem b3Rest2_exists_dual (γ : b3_SmoothLoop E C) :
    ∃ η : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth η ∧ b3Forms_d η = 0 ∧
      (∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth α → b3Forms_d α = 0 →
        b3Forms_integral (b3Rest_b hE) (b3Forms_wedgeForm α η) =
          b3Forms_lineIntegral α γ.1 0 1) := by
  obtain ⟨η, hη, hη'⟩ := b3Rest_exists_dual hE γ.2.2 γ.2.1
  exact ⟨η, hη, b3Rest2_d_eq_zero_of_dual hE γ.2.2 γ.2.1 hη hη', hη'⟩

/-- **`Q(λ_γ, λ_δ) = ∫_δ η_γ`** for every dual form `η_γ` of `γ`. -/
theorem b3Rest2_Q_eq_lineIntegral (γ δ : b3_SmoothLoop E C) {η : C → E [⋀^Fin 1]→L[ℝ] ℝ}
    (hη : b3Forms_IsSmooth η)
    (hη' : ∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth α → b3Forms_d α = 0 →
      b3Forms_integral (b3Rest_b hE) (b3Forms_wedgeForm α η) = b3Forms_lineIntegral α γ.1 0 1) :
    b3Rest2_Q hE (b3_latticePeriod E C γ) (b3_latticePeriod E C δ) =
      b3Forms_lineIntegral η δ.1 0 1 := by
  have hdη := b3Rest2_d_eq_zero_of_dual hE γ.2.2 γ.2.1 hη hη'
  haveI : Fact (Module.finrank ℂ E = 1) := ⟨hE⟩
  obtain ⟨θ, g, hg, heq⟩ := b3Rest_hodge hη hdη
  have hθ := b3Rest2_θ_eq_of_dual hE γ hη hη' hg heq
  rw [b3Rest2_Q, ← hθ]
  show (b3_period E C δ θ).re = _
  rw [b3Rest2_re_period, heq, b3Forms_lineIntegral_add (b3Forms_isSmooth_reForm θ) hg.d δ.2.2,
    b3Forms_lineIntegral_d hg δ.2.2]
  have : δ.1 1 = δ.1 0 := by simpa using δ.2.1 0
  rw [this, sub_self, add_zero]

end HodgeLean.Foundations.Program
