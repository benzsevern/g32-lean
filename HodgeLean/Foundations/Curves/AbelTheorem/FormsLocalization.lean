import HodgeLean.Foundations.Curves.AbelTheorem.MeromorphicRegularForms

noncomputable section
open HodgeLean.Foundations.Program
open Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]

theorem local_form_germ_eq {k : ℕ}
    (α β : C → E [⋀^Fin k]→L[ℝ] ℝ) (x : C) (hα : α =ᶠ[𝓝 x] β) :
    b3Forms_loc α x =ᶠ[𝓝 (chartAt E x x)] b3Forms_loc β x := by
  have ht : Tendsto (chartAt E x).symm (𝓝 (chartAt E x x)) (𝓝 x) := by
    have hh := ((chartAt E x).continuousAt_symm
      ((chartAt E x).map_source (mem_chart_source E x))).tendsto
    rwa [(chartAt E x).left_inv (mem_chart_source E x)] at hh
  filter_upwards [hα.comp_tendsto ht] with u hu
  change α ((chartAt E x).symm u) = β ((chartAt E x).symm u) at hu
  simp only [b3Forms_loc, hu]

theorem local_form_smooth_of_zero_germ {k : ℕ}
    (α : C → E [⋀^Fin k]→L[ℝ] ℝ) (x : C) (hα : α =ᶠ[𝓝 x] 0) :
    ContDiffAt ℝ ∞ (b3Forms_loc α x) (chartAt E x x) := by
  apply (contDiffAt_const (c := (0 : E [⋀^Fin k]→L[ℝ] ℝ))).congr_of_eventuallyEq
  have he := local_form_germ_eq α 0 x hα
  filter_upwards [he] with u hu
  simpa only [b3Forms_loc_zero, Pi.zero_apply] using hu

theorem wedge_form_smooth_away_from_singular_set
    (S : Set C) (α β : C → E [⋀^Fin 1]→L[ℝ] ℝ)
    (hα : b3Forms_IsSmooth α)
    (hzero : ∀ x ∈ S, α =ᶠ[𝓝 x] 0)
    (hβ : ∀ x ∉ S, ContDiffAt ℝ ∞ (b3Forms_loc β x) (chartAt E x x)) :
    b3Forms_IsSmooth (b3Forms_wedgeForm α β) := by
  letI : IsManifold 𝓘(ℝ, E) ∞ C := b3Forms_isManifold_real
  apply b4c_residue_smooth_of_centres
  intro x
  by_cases hx : x ∈ S
  · apply local_form_smooth_of_zero_germ
    filter_upwards [hzero x hx] with y hy
    ext v
    simp only [b3Forms_wedgeForm, b3Forms_wedge_apply, hy, Pi.zero_apply,
      ContinuousAlternatingMap.coe_zero, zero_mul, sub_self]
  · rw [b3Forms_loc_wedgeForm]
    exact (b3Forms_wedgeL.contDiff.contDiffAt.comp _
      ((hα x).contDiffAt ((chartAt E x).open_target.mem_nhds
        ((chartAt E x).map_source (mem_chart_source E x))))).clm_apply (hβ x hx)

end HodgeLean.Foundations.Curves.AbelTheorem
