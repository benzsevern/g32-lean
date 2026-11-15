import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cRealComparison

noncomputable section

namespace HodgeLean.Foundations.Program

open Manifold Filter Topology Set
open scoped Manifold ContDiff Topology

theorem b6m_mdifferentiableAt_real_of_unramified_comp {C D X : Type}
    [TopologicalSpace C] [TopologicalSpace D] [TopologicalSpace X]
    [ChartedSpace ℂ C] [ChartedSpace ℂ D] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [IsManifold 𝓘(ℂ, ℂ) ω X]
    (e : C → D) (he : Continuous e) (f : C → X) (k : D → X) (x : C)
    (hf : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f x)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (hp : ∀ y, k (e y) = f y)
    (hkd : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k (e x) ≠ 0) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e x := by
  let φ := extChartAt 𝓘(ℂ, ℂ) x
  let ψ := extChartAt 𝓘(ℂ, ℂ) (e x)
  let G := writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x e
  let K := writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (e x) k
  have hGx : G (φ x) = ψ (e x) := by
    change ψ (e (φ.symm (φ x))) = ψ (e x)
    rw [show φ.symm (φ x) = x from extChartAt_to_inv x]
  have hφ : Tendsto φ.symm (𝓝 (φ x)) (𝓝 x) := by
    have hc := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℂ, ℂ)) (n := ω) x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))).continuousAt
    simpa only [extChartAt_to_inv] using hc.tendsto
  have heφ : Tendsto (e ∘ φ.symm) (𝓝 (φ x)) (𝓝 (e x)) :=
    he.continuousAt.tendsto.comp hφ
  have hGc : ContinuousAt G (φ x) := by
    change Tendsto G (𝓝 (φ x)) (𝓝 (G (φ x)))
    rw [hGx]
    exact (contMDiffAt_extChartAt (I := 𝓘(ℂ, ℂ)) (n := ω) (x := e x)).continuousAt.tendsto.comp heφ
  have hK : AnalyticAt ℂ K (G (φ x)) := by
    rw [hGx]
    exact b4cov_analyticOnNhd k hk (e x) _ (b4cov_mem_good k (e x))
  have hKd : fderiv ℂ K (G (φ x)) ≠ 0 := by
    rw [hGx]
    exact hkd ∘ (b4cov_mfderiv_eq_zero_iff k hk (e x) (e x)
      (mem_extChartAt_source _) (mem_extChartAt_source _)).mpr
  have heq : K ∘ G =ᶠ[𝓝 (φ x)] writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x f := by
    have hsrc : ψ.source ∈ 𝓝 (e x) := extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) (e x)
    filter_upwards [heφ.eventually hsrc] with z hz
    change e (φ.symm z) ∈ ψ.source at hz
    change extChartAt 𝓘(ℂ, ℂ) (k (e x)) (k (ψ.symm (ψ (e (φ.symm z))))) = _
    rw [ψ.left_inv hz, hp, hp]
    rfl
  have hF : DifferentiableAt ℝ
      (writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x f) (φ x) := by
    rw [mdifferentiableAt_iff] at hf
    have H := hf.2
    simpa only [φ, writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      range_id, differentiableWithinAt_univ] using H
  have hG := b6m_differentiableAt_real_of_analytic_comp hGc hK hKd
    (hF.congr_of_eventuallyEq heq)
  rw [mdifferentiableAt_iff]
  refine ⟨he.continuousAt, ?_⟩
  simpa only [G, φ, writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    range_id, differentiableWithinAt_univ] using hG

theorem b6m_holomorphic_real_mfderiv_orientation {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    {f : C → D} {x : C} (hf : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)
    (hfd : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x ≠ 0) (v w : ℂ) :
    SignType.sign (b3_orient ℂ
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f x v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f x w)) =
      SignType.sign (b3_orient ℂ v w) := by
  have h := b3A_mdifferentiableAt_real hf
  rw [h.2 v, h.2 w]
  exact b6m_orient_sign_complexLinear _ (b6m_complexLinear_injective_of_ne_zero _ hfd) v w

set_option backward.isDefEq.respectTransparency false in
theorem b6m_surface_comparison_orientation {C D X : Type}
    [TopologicalSpace C] [TopologicalSpace D] [TopologicalSpace X]
    [ChartedSpace ℂ C] [ChartedSpace ℂ D] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [IsManifold 𝓘(ℂ, ℂ) ω X]
    (e : C → D) (he : Continuous e) (f : C → X) (k : D → X) (h : X → X)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (hp : ∀ y, k (e y) = h (f y)) (x : C)
    (hfd : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x ≠ 0)
    (hkd : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k (e x) ≠ 0)
    (hh : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) h (f x))
    (ho : ∀ v w : ℂ, SignType.sign (b3_orient ℂ
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) h (f x) v)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) h (f x) w)) = SignType.sign (b3_orient ℂ v w)) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e x ∧ ∀ v w : ℂ,
      SignType.sign (b3_orient ℂ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e x v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e x w)) = SignType.sign (b3_orient ℂ v w) := by
  have hfC := (hf x).mdifferentiableAt (by simp)
  have hkC := (hk (e x)).mdifferentiableAt (by simp)
  have hfR := (b3A_mdifferentiableAt_real hfC).1
  have hkR := (b3A_mdifferentiableAt_real hkC).1
  have heR := b6m_mdifferentiableAt_real_of_unramified_comp e he (h ∘ f) k x
    (hh.comp x hfR) hk hp hkd
  have hc : ∀ v : ℂ,
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) k (e x) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e x v) =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) h (f x) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f x v) := by
    intro v
    have H := mfderiv_comp_apply x hkR heR v
    rw [show k ∘ e = h ∘ f from funext hp] at H
    exact H.symm.trans (mfderiv_comp_apply x hh hfR v)
  refine ⟨heR, fun v w ↦ ?_⟩
  rw [← b6m_holomorphic_real_mfderiv_orientation hkC hkd
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e x v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e x w), hc v, hc w, ho]
  exact b6m_holomorphic_real_mfderiv_orientation hfC hfd v w

end HodgeLean.Foundations.Program
