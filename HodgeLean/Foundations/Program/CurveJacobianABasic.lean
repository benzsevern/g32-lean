import HodgeLean.Foundations.Program.CurveJacobianDefs

/-! # Track B3, lane A: real and complex derivatives on a Riemann surface

A Riemann surface `C` is charted on a complex line `E`, and the same charts serve the real models
`𝓘(ℝ, E)`. This file compares the two: a holomorphic map is real smooth with the same derivative,
a `C¹` path read in any chart is `C¹` with derivative the image of its velocity, and the velocity of
a `C¹` path is continuous into the complex tangent bundle.
-/

noncomputable section

open Manifold Filter Topology
open scoped ContDiff

namespace HodgeLean.Foundations.Program

section Real

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C]
variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {C' : Type} [TopologicalSpace C'] [ChartedSpace E' C']

/-- A holomorphic map is real smooth in the same charts. -/
theorem b3A_contMDiffWithinAt_real {n : WithTop ℕ∞} {f : C → C'} {s : Set C} {x : C}
    (hf : ContMDiffWithinAt 𝓘(ℂ, E) 𝓘(ℂ, E') n f s x) :
    ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E') n f s x := by
  rw [contMDiffWithinAt_iff] at hf ⊢
  refine ⟨hf.1, ?_⟩
  have := hf.2.restrict_scalars ℝ
  simpa [extChartAt_coe, extChartAt_coe_symm] using this

/-- A complex differentiable map is real differentiable, with the same derivative. -/
theorem b3A_mdifferentiableAt_real {f : C → C'} {x : C}
    (hf : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E') f x) :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E') f x ∧
      ∀ v : E, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') f x v = mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x v := by
  have hf' := hf
  rw [mdifferentiableAt_iff] at hf
  have h2 := hf.2
  simp only [extChartAt_coe, modelWithCornersSelf_coe, Set.range_id,
    differentiableWithinAt_univ] at h2
  have hR : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E') f x := by
    rw [mdifferentiableAt_iff]
    refine ⟨hf.1, ?_⟩
    simpa [extChartAt_coe, extChartAt_coe_symm] using (h2.restrictScalars ℝ).differentiableWithinAt
  refine ⟨hR, fun v ↦ ?_⟩
  rw [hR.mfderiv, hf'.mfderiv]
  simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    Set.range_id, fderivWithin_univ, modelWithCornersSelf_coe_symm] at h2 ⊢
  change (fderiv ℝ _ _ : E →L[ℝ] E') v = (fderiv ℂ _ _ : E →L[ℂ] E') v
  exact congrArg (fun L : E →L[ℝ] E' ↦ L v) (h2.fderiv_restrictScalars ℝ)

/-- The velocity as a function `ℝ → E` (the tangent spaces are all `E`). -/
def b3A_vel (γ : ℝ → C) (t : ℝ) : E := b3_velocity E C γ t

/-- The velocity of a differentiable path is the derivative of the path read in the chart at its
point. -/
theorem b3A_velocity_eq_fderiv (γ : ℝ → C) (t : ℝ) (hm : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) :
    b3_velocity E C γ t = fderiv ℝ (chartAt E (γ t) ∘ γ) t 1 := by
  rw [b3_velocity, hm.mfderiv]
  simp [writtenInExtChartAt, tangentSpaceCastModel]
  exact one_smul ℝ _

end Real

section Velocity

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The chart transition `φ_{x₀} ∘ φ_x⁻¹` is complex differentiable at `φ_x y` when `y` lies in both
chart sources. -/
theorem b3A_transition_contDiffAt (x₀ x y : C) (hy : y ∈ (chartAt E x).source)
    (hy₀ : y ∈ (chartAt E x₀).source) :
    ContDiffAt ℂ ω (chartAt E x₀ ∘ (chartAt E x).symm) (chartAt E x y) := by
  have h := contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ, E)) (n := ω) x₀ x
    (y := chartAt E x y) (by simp [hy, hy₀])
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe, Set.range_id,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, contDiffWithinAt_univ] at h
  exact h

/-- A `C¹` path read in any chart containing its point is `C¹`, and its derivative is the image of
the velocity under the transition. -/
theorem b3A_chart_comp (γ : ℝ → C) (s : ℝ) (hγ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ s)
    (x₀ : C) (hs : γ s ∈ (chartAt E x₀).source) :
    ContDiffAt ℝ 1 (chartAt E x₀ ∘ γ) s ∧
      fderiv ℝ (chartAt E x₀ ∘ γ) s 1 =
        fderiv ℂ (chartAt E x₀ ∘ (chartAt E (γ s)).symm) (chartAt E (γ s) (γ s))
          (b3_velocity E C γ s) := by
  rw [contMDiffAt_iff] at hγ
  obtain ⟨hc, hd⟩ := hγ
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe, Set.range_id,
    contDiffWithinAt_univ, chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.refl_apply, Function.comp_id, Function.id_comp, id_eq,
    modelWithCornersSelf_coe_symm] at hd
  have hT := b3A_transition_contDiffAt x₀ (γ s) (γ s) (mem_chart_source E _) hs
  have hTR : ContDiffAt ℝ 1 (chartAt E x₀ ∘ (chartAt E (γ s)).symm) (chartAt E (γ s) (γ s)) :=
    (hT.restrict_scalars ℝ).of_le le_top
  have hev : chartAt E x₀ ∘ γ =ᶠ[𝓝 s]
      (chartAt E x₀ ∘ (chartAt E (γ s)).symm) ∘ (chartAt E (γ s) ∘ γ) := by
    filter_upwards [hc.preimage_mem_nhds ((chartAt E (γ s)).open_source.mem_nhds
      (mem_chart_source E _))] with u hu
    simp [(chartAt E (γ s)).left_inv hu]
  refine ⟨(hTR.comp s hd).congr_of_eventuallyEq hev, ?_⟩
  have hm : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s := by
    rw [mdifferentiableAt_iff]
    refine ⟨hc, ?_⟩
    simpa [extChartAt_coe, extChartAt_coe_symm] using
      (hd.differentiableAt one_ne_zero).differentiableWithinAt
  have hv := b3A_velocity_eq_fderiv γ s hm
  rw [hev.fderiv_eq, fderiv_comp s (hTR.differentiableAt one_ne_zero)
    (hd.differentiableAt one_ne_zero), hv]
  show fderiv ℝ (chartAt E x₀ ∘ (chartAt E (γ s)).symm) (chartAt E (γ s) (γ s))
    (fderiv ℝ (chartAt E (γ s) ∘ γ) s 1) = _
  rw [(hT.differentiableAt (by simp)).fderiv_restrictScalars ℝ]
  rfl

/-- The velocity of a `C¹` path is continuous into the complex tangent bundle. -/
theorem b3A_continuous_velocity (γ : ℝ → C) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) :
    Continuous (fun t ↦ (⟨γ t, b3_velocity E C γ t⟩ : TangentBundle 𝓘(ℂ, E) C)) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hγ.continuous.continuousAt, ?_⟩
  set x₀ := γ t₀
  set U := γ ⁻¹' (chartAt E x₀).source
  have hU : IsOpen U := (chartAt E x₀).open_source.preimage hγ.continuous
  have ht₀ : t₀ ∈ U := mem_chart_source E x₀
  have hcd : ContDiffOn ℝ 1 (chartAt E x₀ ∘ γ) U := fun t ht ↦
    (b3A_chart_comp γ t (hγ t) x₀ ht).1.contDiffWithinAt
  have hcont : ContinuousOn (fun t ↦ fderiv ℝ (chartAt E x₀ ∘ γ) t 1) U :=
    (hcd.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  refine ((hcont.continuousAt (hU.mem_nhds ht₀))).congr ?_
  filter_upwards [hU.mem_nhds ht₀] with t ht
  rw [(b3A_chart_comp γ t (hγ t) x₀ ht).2]
  simp [TangentBundle.trivializationAt_apply, x₀]

end Velocity

end HodgeLean.Foundations.Program
