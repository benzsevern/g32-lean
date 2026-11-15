import HodgeLean.Foundations.Program.CurveJacobianDefs
import HodgeLean.Foundations.Program.RelativeTorusTopology

/-! # B4 algebraic lane: holomorphic forms on compact complex tori

On `b2_torus Λ F` the chart transitions are translations, so the tangent bundle is trivial in every
chart. This file proves that straight lines `u ↦ [u w + c]` are `C¹` with constant velocity, that
translation-invariant forms `(x, v) ↦ ℓ v` are holomorphic, and that on a compact connected torus
every holomorphic `1`-form is translation-invariant (so `dim Ω¹ = g`).
-/

noncomputable section

open Manifold Filter Topology
open scoped ContDiff TensorProduct

namespace HodgeLean.Foundations.Program

section Torus

variable {Λ : Type} [AddCommGroup Λ]

/-- The model `ℂ^g` of B2's torus `b2_torus Λ F`. -/
abbrev HurwitzPrymAlg2_TM (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) : Type :=
  Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ

variable [Module.Finite ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
  [DiscreteTopology (b2_latticeMap Λ F).range]

/-- The chart transitions of the torus are translations near each point. -/
theorem HurwitzPrymAlg2_torus_transition (x₀ x : b2_torus Λ F) (hx : x ∈ (chartAt (HurwitzPrymAlg2_TM F) x₀).source) :
    ∃ a : HurwitzPrymAlg2_TM F, ∀ᶠ z in 𝓝 (chartAt (HurwitzPrymAlg2_TM F) x x),
      chartAt (HurwitzPrymAlg2_TM F) x₀ ((chartAt (HurwitzPrymAlg2_TM F) x).symm z) = z + a := by
  have hy : (QuotientAddGroup.mk ((b2_coordHomeomorph Λ F).symm (chartAt (HurwitzPrymAlg2_TM F) x x)) :
      b2_torus Λ F) ∈ (b2_torusChart Λ F x₀).source := by
    have := (chartAt (HurwitzPrymAlg2_TM F) x).left_inv (mem_chart_source (HurwitzPrymAlg2_TM F) x)
    rw [show (chartAt (HurwitzPrymAlg2_TM F) x).symm = (b2_torusChart Λ F x).symm from rfl,
      b2t_torusChart_symm_apply] at this
    rw [this]
    exact hx
  obtain ⟨a, ha⟩ := b2t_torusChart_eventually F x₀
    (b2_coordHomeomorph Λ F).symm.continuous.continuousAt hy
  refine ⟨a, ?_⟩
  filter_upwards [ha] with z hz
  rw [show (chartAt (HurwitzPrymAlg2_TM F) x).symm = (b2_torusChart Λ F x).symm from rfl,
    b2t_torusChart_symm_apply]
  erw [hz]
  congr 1
  exact (b2_coordHomeomorph Λ F).apply_symm_apply z

/-- The chart transitions of the torus have derivative the identity. -/
theorem HurwitzPrymAlg2_torus_fderiv_transition (x₀ x : b2_torus Λ F)
    (hx : x ∈ (chartAt (HurwitzPrymAlg2_TM F) x₀).source) :
    fderiv ℂ (chartAt (HurwitzPrymAlg2_TM F) x₀ ∘ (chartAt (HurwitzPrymAlg2_TM F) x).symm) (chartAt (HurwitzPrymAlg2_TM F) x x) =
      ContinuousLinearMap.id ℂ (HurwitzPrymAlg2_TM F) := by
  obtain ⟨a, ha⟩ := HurwitzPrymAlg2_torus_transition F x₀ x hx
  have : (chartAt (HurwitzPrymAlg2_TM F) x₀ ∘ (chartAt (HurwitzPrymAlg2_TM F) x).symm) =ᶠ[𝓝 (chartAt (HurwitzPrymAlg2_TM F) x x)]
      (fun z ↦ z + a) := ha
  rw [this.fderiv_eq]
  simp

variable [IsManifold 𝓘(ℂ, HurwitzPrymAlg2_TM F) ω (b2_torus Λ F)]

/-- In every tangent-bundle trivialization of the torus the fibre coordinate is the vector itself. -/
theorem HurwitzPrymAlg2_torus_triv_snd (x₀ : b2_torus Λ F) (p : TangentBundle 𝓘(ℂ, HurwitzPrymAlg2_TM F) (b2_torus Λ F))
    (hp : p.1 ∈ (chartAt (HurwitzPrymAlg2_TM F) x₀).source) :
    (trivializationAt (HurwitzPrymAlg2_TM F) (TangentSpace 𝓘(ℂ, HurwitzPrymAlg2_TM F)) x₀ p).2 = p.2 := by
  rw [TangentBundle.trivializationAt_apply]
  simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id, fderivWithin_univ,
    CompTriple.comp_eq]
  rw [HurwitzPrymAlg2_torus_fderiv_transition F x₀ p.1 hp]
  rfl

/-- **The translation-invariant form** `(x, v) ↦ ℓ v` of a linear functional `ℓ`. -/
def HurwitzPrymAlg2_invForm (ℓ : HurwitzPrymAlg2_TM F →L[ℂ] ℂ) : TangentBundle 𝓘(ℂ, HurwitzPrymAlg2_TM F) (b2_torus Λ F) → ℂ :=
  fun p ↦ ℓ p.2

/-- Translation-invariant forms are holomorphic `1`-forms. -/
theorem HurwitzPrymAlg2_invForm_mem (ℓ : HurwitzPrymAlg2_TM F →L[ℂ] ℂ) :
    HurwitzPrymAlg2_invForm F ℓ ∈ b3_HolForm (HurwitzPrymAlg2_TM F) (b2_torus Λ F) := by
  refine ⟨fun p ↦ ?_, fun x a v w ↦ ?_⟩
  swap
  · exact (ℓ.map_add (a • v) w).trans (congrArg (· + ℓ w) (ℓ.map_smul a v))
  set e := trivializationAt (HurwitzPrymAlg2_TM F) (TangentSpace 𝓘(ℂ, HurwitzPrymAlg2_TM F)) p.1
  have hp : p ∈ e.source := by
    rw [TangentBundle.trivializationAt_source]
    exact mem_chart_source (HurwitzPrymAlg2_TM F) p.proj
  have h1 := (e.contMDiffOn (n := ω) (IB := 𝓘(ℂ, HurwitzPrymAlg2_TM F)) p hp).contMDiffAt
    (e.open_source.mem_nhds hp)
  have h2 : ContMDiff (𝓘(ℂ, HurwitzPrymAlg2_TM F).prod 𝓘(ℂ, HurwitzPrymAlg2_TM F)) 𝓘(ℂ, ℂ) ω
      (fun q : b2_torus Λ F × HurwitzPrymAlg2_TM F ↦ ℓ q.2) :=
    ℓ.contMDiff.comp contMDiff_snd
  refine ((h2 _).comp p h1).congr_of_eventuallyEq ?_
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  rw [TangentBundle.trivializationAt_source] at hq
  simp only [Function.comp_apply, HurwitzPrymAlg2_invForm, e, HurwitzPrymAlg2_torus_triv_snd F p.1 q hq]

/-- The constant section `x ↦ (x, c)` of the tangent bundle of the torus is holomorphic. -/
theorem HurwitzPrymAlg2_constSection_contMDiff (c : HurwitzPrymAlg2_TM F) :
    ContMDiff 𝓘(ℂ, HurwitzPrymAlg2_TM F) 𝓘(ℂ, HurwitzPrymAlg2_TM F).tangent ω
      (fun x : b2_torus Λ F ↦ (⟨x, c⟩ : TangentBundle 𝓘(ℂ, HurwitzPrymAlg2_TM F) (b2_torus Λ F))) := by
  intro x₀
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_id, (contMDiffAt_const (c := c)).congr_of_eventuallyEq ?_⟩
  filter_upwards [(chartAt (HurwitzPrymAlg2_TM F) x₀).open_source.mem_nhds (mem_chart_source _ x₀)] with x hx
  exact HurwitzPrymAlg2_torus_triv_snd F x₀ ⟨x, c⟩ hx

/-- **Holomorphic forms on a compact connected torus are translation-invariant**: `x ↦ θ (x, v)`
is a holomorphic function on a compact connected manifold, hence constant. -/
theorem HurwitzPrymAlg2_torus_form_apply [CompactSpace (b2_torus Λ F)] [ConnectedSpace (b2_torus Λ F)]
    (θ : TangentBundle 𝓘(ℂ, HurwitzPrymAlg2_TM F) (b2_torus Λ F) → ℂ)
    (hθ : θ ∈ b3_HolForm (HurwitzPrymAlg2_TM F) (b2_torus Λ F)) (x : b2_torus Λ F) (v : HurwitzPrymAlg2_TM F) :
    θ ⟨x, v⟩ = θ ⟨0, v⟩ := by
  have hf : ContMDiff 𝓘(ℂ, HurwitzPrymAlg2_TM F) 𝓘(ℂ, ℂ) ω (fun y : b2_torus Λ F ↦ θ ⟨y, v⟩) :=
    hθ.1.comp (HurwitzPrymAlg2_constSection_contMDiff F v)
  exact (hf.mdifferentiable (by simp)).apply_eq_of_compactSpace x 0

/-- The linear functional of a holomorphic form at the origin. -/
def HurwitzPrymAlg2_formFunctional (θ : b3_HolForm (HurwitzPrymAlg2_TM F) (b2_torus Λ F)) : HurwitzPrymAlg2_TM F →ₗ[ℂ] ℂ where
  toFun v := (θ : TangentBundle 𝓘(ℂ, HurwitzPrymAlg2_TM F) (b2_torus Λ F) → ℂ) ⟨0, v⟩
  map_add' v w := by
    have := θ.2.2 0 1 v w
    rw [one_mul] at this
    rw [← this]
    exact (one_smul ℂ v).symm ▸ rfl
  map_smul' a v := by
    have h0 := θ.2.2 0 1 0 0
    have := θ.2.2 0 a v 0
    simp only [one_smul, add_zero, one_mul] at h0 this
    have hz : (θ : TangentBundle 𝓘(ℂ, HurwitzPrymAlg2_TM F) (b2_torus Λ F) → ℂ) ⟨0, 0⟩ = 0 := by
      linear_combination -h0
    rw [hz, add_zero] at this
    exact this

/-- Every holomorphic form on a compact connected torus is translation-invariant. -/
theorem HurwitzPrymAlg2_torus_form_eq [CompactSpace (b2_torus Λ F)] [ConnectedSpace (b2_torus Λ F)]
    (θ : b3_HolForm (HurwitzPrymAlg2_TM F) (b2_torus Λ F)) :
    (θ : TangentBundle 𝓘(ℂ, HurwitzPrymAlg2_TM F) (b2_torus Λ F) → ℂ) =
      HurwitzPrymAlg2_invForm F (LinearMap.toContinuousLinearMap (HurwitzPrymAlg2_formFunctional F θ)) := by
  funext p
  exact HurwitzPrymAlg2_torus_form_apply F θ θ.2 p.1 p.2

/-- On a compact connected torus, holomorphic forms are the linear functionals on the model. -/
def HurwitzPrymAlg2_torus_formEquiv [CompactSpace (b2_torus Λ F)] [ConnectedSpace (b2_torus Λ F)] :
    b3_HolForm (HurwitzPrymAlg2_TM F) (b2_torus Λ F) ≃ₗ[ℂ] Module.Dual ℂ (HurwitzPrymAlg2_TM F) where
  toFun := HurwitzPrymAlg2_formFunctional F
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun ℓ := ⟨HurwitzPrymAlg2_invForm F (LinearMap.toContinuousLinearMap ℓ),
    HurwitzPrymAlg2_invForm_mem F (LinearMap.toContinuousLinearMap ℓ)⟩
  left_inv θ := Subtype.ext (HurwitzPrymAlg2_torus_form_eq F θ).symm
  right_inv _ := rfl

/-- `dim Ω¹ = g` on a compact connected torus. -/
theorem HurwitzPrymAlg2_torus_finrank_holForm [CompactSpace (b2_torus Λ F)] [ConnectedSpace (b2_torus Λ F)] :
    Module.finrank ℂ (b3_HolForm (HurwitzPrymAlg2_TM F) (b2_torus Λ F)) =
      Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F) := by
  rw [(HurwitzPrymAlg2_torus_formEquiv F).finrank_eq, Subspace.dual_finrank_eq]
  simp

end Torus

end HodgeLean.Foundations.Program

