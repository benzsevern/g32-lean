import HodgeLean.Foundations.Program.RelativeFrameOperatorCutoff

set_option maxHeartbeats 400000

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

theorem rf4_smoothCoeff_differentiableAt (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] {p q : ℕ} (v : rf2_smoothForms X p q) (x : X)
    (z : (chartAt ℂ x).target) : DifferentiableAt ℝ (rf2_extend X v.val x) z := by
  obtain ⟨g, hg, hv⟩ := v.property.1 x
  apply (((hg z z.property).contDiffAt ((chartAt ℂ x).open_target.mem_nhds z.property)).differentiableAt
    (by simp)).congr_of_eventuallyEq
  filter_upwards [(chartAt ℂ x).open_target.mem_nhds z.property] with u hu
  simp only [rf2_extend, dite_eq_left hu]
  exact hv ⟨u, hu⟩

theorem rf4_dbar10_smul (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (c : ℂ) (v : rf2_smoothForms X 1 0) :
    rf2_dbar10 X (c • v).val = c • rf2_dbar10 X v.val := by
  classical
  funext x z
  have he : rf2_extend X (c • v).val x = fun u ↦ c * rf2_extend X v.val x u := by
    funext u
    by_cases hu : u ∈ (chartAt ℂ x).target <;> simp [rf2_extend, hu, smul_eq_mul]
  have hd := rf4_smoothCoeff_differentiableAt X v x z
  change -wirtingerDbar (rf2_extend X (c • v).val x) z =
    c * (-wirtingerDbar (rf2_extend X v.val x) z)
  rw [he, rf2_wirtingerDbar_mul (differentiableAt_const c) hd]
  have hc : wirtingerDbar (fun _ : ℂ ↦ c) z = 0 := by simp [wirtingerDbar]
  rw [hc, mul_zero, add_zero]
  ring

theorem rf4_dbar10_add (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (v w : rf2_smoothForms X 1 0) :
    rf2_dbar10 X (v + w).val = rf2_dbar10 X v.val + rf2_dbar10 X w.val := by
  simpa [Fin.sum_univ_two] using rf2_dbar10_sum X Finset.univ ![v, w]

def rf4_dbar10Linear (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] : rf2_smoothForms X 1 0 →ₗ[ℂ] rf2_Coeff X where
  toFun v := rf2_dbar10 X v.val
  map_add' := rf4_dbar10_add X
  map_smul' := rf4_dbar10_smul X

theorem rf4_dbar10_image_span (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] :
    (Submodule.span ℂ (rf2_dbar10 X '' (rf2_smoothForms X 1 0 : Set (rf2_Coeff X))) :
      Set (rf2_Coeff X)) = rf2_dbar10 X '' (rf2_smoothForms X 1 0 : Set (rf2_Coeff X)) := by
  let L := rf4_dbar10Linear X
  have he : rf2_dbar10 X '' (rf2_smoothForms X 1 0 : Set (rf2_Coeff X)) =
      (L.range : Set _) := by
    ext f
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨u, u.property, rfl⟩
  rw [he, Submodule.span_eq]

theorem rf4_boundary_representative (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (σ : rf2_smoothForms X 1 1)
    (hσ : (Submodule.Quotient.mk σ : rf2_smoothForms X 1 1 ⧸ rf2_boundaries X) = 0) :
    ∃ v : rf2_smoothForms X 1 0, rf2_dbar10 X v.val = σ.val := by
  have hm := (Submodule.Quotient.mk_eq_zero (rf2_boundaries X)).mp hσ
  change σ.val ∈ Submodule.span ℂ
    (rf2_dbar10 X '' (rf2_smoothForms X 1 0 : Set (rf2_Coeff X))) at hm
  rw [← SetLike.mem_coe, rf4_dbar10_image_span X] at hm
  obtain ⟨v, hv, he⟩ := hm
  exact ⟨⟨v, hv⟩, he⟩

end HodgeLean.Foundations.Program
