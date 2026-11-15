import HodgeLean.Foundations.Program.CurveJacobianFormsStokes

/-!
# Track B3 foundations (stage B3.6b): the Leibniz rule and the pairing on `H¹_dR`

* `b3Forms_extDeriv_smul`, `b3Forms_d_smulFun`: the Leibniz rule `d(g β) = dg ∧ β + g dβ` for a
  function `g` and a `1`-form `β`, flat and on a manifold;
* `b3Forms_integral_wedge_d_eq_zero`: on a compact oriented surface `∫ dg ∧ β = 0` for closed `β`,
  so that `b3Forms_pairing`, `(α, β) ↦ ∫_M α ∧ β`, descends to closed forms modulo exact forms
  (`b3Forms_deRhamPairing`, a bilinear form on `H¹_dR(M)`). -/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Function
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

section Flat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The Leibniz rule** for a function times a `1`-form on a normed space. -/
theorem b3Forms_extDeriv_smul {f : E → ℝ} {β : E → E [⋀^Fin 1]→L[ℝ] ℝ} {u : E}
    (hf : DifferentiableAt ℝ f u) (hβ : DifferentiableAt ℝ β u) :
    extDeriv (fun y ↦ f y • β y) u =
      b3Forms_wedge (ofSubsingleton ℝ E ℝ (0 : Fin 1) (fderiv ℝ f u)) (β u) +
        f u • extDeriv β u := by
  simp only [extDeriv, fderiv_fun_smul hf hβ, alternatizeUncurryFin_add,
    alternatizeUncurryFin_smul, b3Forms_wedge, Equiv.symm_apply_apply]
  exact add_comm _ _

end Flat

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **The Leibniz rule** `d(g β) = dg ∧ β + g dβ` for a smooth function `g` and a smooth
`1`-form `β`. -/
theorem b3Forms_d_smulFun {g : M → ℝ} (hg : b3Forms_IsSmooth (b3Forms_fun (E := E) g))
    {β : M → E [⋀^Fin 1]→L[ℝ] ℝ} (hβ : b3Forms_IsSmooth β) :
    b3Forms_d (b3Forms_smulFun g β) =
      b3Forms_wedgeForm (b3Forms_d (b3Forms_fun (E := E) g)) β +
        b3Forms_smulFun g (b3Forms_d β) := by
  funext z
  have hz := (chartAt E z).map_source (mem_chart_source E z)
  have hgz : ContDiffOn ℝ ∞ (g ∘ (chartAt E z).symm) (chartAt E z).target :=
    (b3Forms_isSmooth_fun_iff g).1 hg z
  have hgd : DifferentiableAt ℝ (g ∘ (chartAt E z).symm) (chartAt E z z) :=
    (hgz.contDiffAt ((chartAt E z).open_target.mem_nhds hz)).differentiableAt (by simp)
  have hβd : DifferentiableAt ℝ (b3Forms_loc β z) (chartAt E z z) :=
    (hβ.contDiffAt hz).differentiableAt (by simp)
  show extDeriv _ _ = _
  rw [b3Forms_loc_smulFun]
  rw [show (fun u ↦ g ((chartAt E z).symm u) • b3Forms_loc β z u) =
    fun u ↦ (g ∘ (chartAt E z).symm) u • b3Forms_loc β z u from rfl,
    b3Forms_extDeriv_smul hgd hβd]
  simp only [Pi.add_apply, b3Forms_wedgeForm, b3Forms_smulFun, b3Forms_d_fun, b3Forms_loc_self,
    Function.comp_apply, (chartAt E z).left_inv (mem_chart_source E z)]
  rfl

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [T2Space M] [CompactSpace M]
  (b : Module.Basis (Fin 2) ℝ E)

/-- **The pairing of `1`-forms** on a compact oriented surface, `(α, β) ↦ ∫_M α ∧ β`.
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, GTM 82, §5 (the Poincaré duality
pairing); Forster, *Lectures on Riemann Surfaces*, GTM 81, §19. -/
def b3Forms_pairing (α β : M → E [⋀^Fin 1]→L[ℝ] ℝ) : ℝ :=
  b3Forms_integral b (b3Forms_wedgeForm α β)

theorem b3Forms_pairing_comm (α β : M → E [⋀^Fin 1]→L[ℝ] ℝ) :
    b3Forms_pairing b β α = -b3Forms_pairing b α β := by
  have : b3Forms_wedgeForm β α = (-1 : ℝ) • b3Forms_wedgeForm α β := by
    funext z
    simp [b3Forms_wedgeForm, b3Forms_wedge_comm (α z)]
  rw [b3Forms_pairing, b3Forms_pairing, this, b3Forms_integral_smul]
  ring

theorem b3Forms_pairing_add_left {α α' β : M → E [⋀^Fin 1]→L[ℝ] ℝ}
    (hα : b3Forms_IsSmooth α) (hα' : b3Forms_IsSmooth α') (hβ : b3Forms_IsSmooth β) :
    b3Forms_pairing b (α + α') β = b3Forms_pairing b α β + b3Forms_pairing b α' β := by
  have : b3Forms_wedgeForm (α + α') β = b3Forms_wedgeForm α β + b3Forms_wedgeForm α' β := by
    funext z
    simp [b3Forms_wedgeForm, b3Forms_wedge_add_left]
  rw [b3Forms_pairing, this, b3Forms_integral_add b (hα.wedgeForm hβ) (hα'.wedgeForm hβ)]
  rfl

theorem b3Forms_pairing_smul_left (c : ℝ) (α β : M → E [⋀^Fin 1]→L[ℝ] ℝ) :
    b3Forms_pairing b (c • α) β = c * b3Forms_pairing b α β := by
  have : b3Forms_wedgeForm (c • α) β = c • b3Forms_wedgeForm α β := by
    funext z
    simp [b3Forms_wedgeForm, b3Forms_wedge_smul_left]
  rw [b3Forms_pairing, this, b3Forms_integral_smul]
  rfl

/-- **An exact form pairs to zero with a closed form**: `∫_M dg ∧ β = ∫_M d(g β) = 0` when
`dβ = 0`, by the Leibniz rule and Stokes' theorem. -/
theorem b3Forms_integral_wedge_d_eq_zero (hor : b3Forms_Oriented E M) {g : M → ℝ}
    (hg : b3Forms_IsSmooth (b3Forms_fun (E := E) g)) {β : M → E [⋀^Fin 1]→L[ℝ] ℝ}
    (hβ : b3Forms_IsSmooth β) (hdβ : b3Forms_d β = 0) :
    b3Forms_pairing b (b3Forms_d (b3Forms_fun (E := E) g)) β = 0 := by
  have h := b3Forms_d_smulFun hg hβ
  rw [hdβ] at h
  have h0 : b3Forms_smulFun g (0 : M → E [⋀^Fin 2]→L[ℝ] ℝ) = 0 := by
    funext z; simp [b3Forms_smulFun]
  rw [h0, add_zero] at h
  rw [b3Forms_pairing, ← h]
  exact b3Forms_integral_d_eq_zero hor b (b3Forms_IsSmooth.smulFun' hg hβ)

/-- The pairing of two closed `1`-forms depends only on their de Rham classes. -/
theorem b3Forms_pairing_add_exact (hor : b3Forms_Oriented E M)
    {α β : M → E [⋀^Fin 1]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α) (hβ : b3Forms_IsSmooth β)
    (hdα : b3Forms_d α = 0) (hdβ : b3Forms_d β = 0) {g h : M → ℝ}
    (hg : b3Forms_IsSmooth (b3Forms_fun (E := E) g))
    (hh : b3Forms_IsSmooth (b3Forms_fun (E := E) h)) :
    b3Forms_pairing b (α + b3Forms_d (b3Forms_fun (E := E) g))
      (β + b3Forms_d (b3Forms_fun (E := E) h)) = b3Forms_pairing b α β := by
  have hdg := hg.d
  have hdh := hh.d
  have hddh : b3Forms_d (b3Forms_d (b3Forms_fun (E := E) h)) = 0 := b3Forms_d_d hh
  have hdsum : b3Forms_d (α + b3Forms_d (b3Forms_fun (E := E) g)) = 0 := by
    rw [b3Forms_d_add hα hdg, hdα, b3Forms_d_d hg, add_zero]
  rw [b3Forms_pairing_comm b, b3Forms_pairing_add_left b hβ hdh (hα.add hdg)]
  rw [b3Forms_integral_wedge_d_eq_zero b hor hh (hα.add hdg) hdsum, add_zero,
    ← b3Forms_pairing_comm b, b3Forms_pairing_add_left b hα hdg hβ,
    b3Forms_integral_wedge_d_eq_zero b hor hg hβ hdβ, add_zero]

theorem b3Forms_pairing_add_right {α β β' : M → E [⋀^Fin 1]→L[ℝ] ℝ}
    (hα : b3Forms_IsSmooth α) (hβ : b3Forms_IsSmooth β) (hβ' : b3Forms_IsSmooth β') :
    b3Forms_pairing b α (β + β') = b3Forms_pairing b α β + b3Forms_pairing b α β' := by
  rw [← neg_neg (b3Forms_pairing b α (β + β')), ← b3Forms_pairing_comm,
    b3Forms_pairing_add_left b hβ hβ' hα, b3Forms_pairing_comm b α β,
    b3Forms_pairing_comm b α β']
  ring

theorem b3Forms_pairing_smul_right (c : ℝ) (α β : M → E [⋀^Fin 1]→L[ℝ] ℝ) :
    b3Forms_pairing b α (c • β) = c * b3Forms_pairing b α β := by
  rw [← neg_neg (b3Forms_pairing b α (c • β)), ← b3Forms_pairing_comm,
    b3Forms_pairing_smul_left, b3Forms_pairing_comm b α β]
  ring

/-- The pairing on closed `1`-forms as a bilinear form.
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, GTM 82, §5 (the Poincaré duality
pairing); Forster, *Lectures on Riemann Surfaces*, GTM 81, §19. -/
def b3Forms_closedPairing : LinearMap.BilinForm ℝ (b3Forms_closed E M 0) :=
  LinearMap.mk₂ ℝ (fun α β ↦ b3Forms_pairing b α.1.1 β.1.1)
    (fun α α' β ↦ b3Forms_pairing_add_left b α.1.2 α'.1.2 β.1.2)
    (fun c α β ↦ b3Forms_pairing_smul_left b c α.1.1 β.1.1)
    (fun α β β' ↦ b3Forms_pairing_add_right b α.1.2 β.1.2 β'.1.2)
    (fun c α β ↦ b3Forms_pairing_smul_right b c α.1.1 β.1.1)

/-- An exact `1`-form pairs to zero with every closed `1`-form. -/
theorem b3Forms_closedPairing_exact (hor : b3Forms_Oriented E M) (α β : b3Forms_closed E M 0)
    (hα : α ∈ (b3Forms_exact E M 0).comap (b3Forms_closed E M 0).subtype) :
    b3Forms_closedPairing b α β = 0 := by
  obtain ⟨γ, hγ⟩ := hα
  have hγ' : α.1.1 = b3Forms_d (b3Forms_fun (E := E) (b3Forms_toFun γ.1)) := by
    rw [b3Forms_fun_toFun]
    exact (congrArg Subtype.val hγ).symm
  show b3Forms_pairing b α.1.1 β.1.1 = 0
  rw [hγ']
  refine b3Forms_integral_wedge_d_eq_zero b hor ?_ β.1.2 (b3Forms_closed_d_eq_zero β)
  rw [b3Forms_fun_toFun]
  exact γ.2

/-- **The pairing on `H¹_dR(M)`**: `([α], [β]) ↦ ∫_M α ∧ β` on a compact oriented surface.
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, GTM 82, §5 (the Poincaré duality
pairing); Forster, *Lectures on Riemann Surfaces*, GTM 81, §19. -/
def b3Forms_deRhamPairing (hor : b3Forms_Oriented E M) :
    LinearMap.BilinForm ℝ (b3Forms_deRham E M 0) :=
  let p := (b3Forms_exact E M 0).comap (b3Forms_closed E M 0).subtype
  let P1 := p.liftQ (b3Forms_closedPairing b) fun α hα ↦ by
    ext β
    exact b3Forms_closedPairing_exact b hor α β hα
  (p.liftQ P1.flip fun β hβ ↦ by
    ext α
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      LinearMap.flip_apply, LinearMap.zero_apply, P1]
    show b3Forms_pairing b α.1.1 β.1.1 = 0
    rw [← neg_neg (b3Forms_pairing b α.1.1 β.1.1), ← b3Forms_pairing_comm, neg_eq_zero]
    exact b3Forms_closedPairing_exact b hor β α hβ).flip

theorem b3Forms_deRhamPairing_mk (hor : b3Forms_Oriented E M) (α β : b3Forms_closed E M 0) :
    b3Forms_deRhamPairing b hor (Submodule.Quotient.mk α) (Submodule.Quotient.mk β) =
      b3Forms_pairing b α.1.1 β.1.1 := rfl

end Manifold

end HodgeLean.Foundations.Program
