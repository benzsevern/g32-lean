import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]

theorem projected_form_smooth_at_center (h : Module.finrank ℂ E = 1)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (hθ : HurwitzPrymRR_IsLinear θ)
    (P : ℂ →L[ℝ] ℝ) (x : C)
    (hs : ContDiffAt ℝ ∞ (HurwitzPrymRR_loc h θ x) 0) :
    ContDiffAt ℝ ∞ (b3Forms_loc (b4c_residue_realForm h θ P) x) (chartAt E x x) := by
  letI : IsManifold 𝓘(ℝ, E) ∞ C := b3Forms_isManifold_real
  let L := b4cov_lineEquiv h
  let A : ℂ → E [⋀^Fin 1]→L[ℝ] ℝ := fun c =>
    ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)
      (P.comp ((c • L.symm.toContinuousLinearMap).restrictScalars ℝ))
  have hA : ContDiff ℝ ∞ A := by
    apply contDiffOn_univ.mp
    apply b3Forms_contDiffOn_of_apply
    intro v
    change ContDiffOn ℝ ∞ (fun c => P (c * L.symm v)) Set.univ
    exact P.contDiff.comp_contDiffOn (contDiffOn_id.mul contDiffOn_const)
  have harg : ContDiffAt ℝ ∞ (fun u : E => L.symm (u - chartAt E x x))
      (chartAt E x x) :=
    (L.symm.contDiff.restrict_scalars ℝ).contDiffAt.comp _
      (contDiffAt_id.sub contDiffAt_const)
  have harg0 : L.symm (chartAt E x x - chartAt E x x) = 0 := by simp
  have hs' : ContDiffAt ℝ ∞ (HurwitzPrymRR_loc h θ x)
      (L.symm (chartAt E x x - chartAt E x x)) := harg0 ▸ hs
  have hg := hs'.comp (chartAt E x x) harg
  have hc := hA.contDiffAt.comp (chartAt E x x) hg
  apply hc.congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_target.mem_nhds
    ((chartAt E x).map_source (mem_chart_source E x))] with u hu
  ext v
  have hv : v = fun _ => v 0 := funext fun i => by fin_cases i; rfl
  rw [hv]
  exact b4c_residue_loc_realForm_coefficient h θ hθ P hu (v 0)

theorem real_differential_zero_of_constant_germ (f : C → ℝ) (x : C) (c : ℝ)
    (hf : f =ᶠ[𝓝 x] fun _ => c) : b3Forms_d (b3Forms_fun (E := E) f) x = 0 := by
  letI : IsManifold 𝓘(ℝ, E) ∞ C := b3Forms_isManifold_real
  rw [b3Forms_d_fun]
  have ht : Tendsto (chartAt E x).symm (𝓝 (chartAt E x x)) (𝓝 x) := by
    have hh := ((chartAt E x).continuousAt_symm
      ((chartAt E x).map_source (mem_chart_source E x))).tendsto
    rwa [(chartAt E x).left_inv (mem_chart_source E x)] at hh
  have he : (f ∘ (chartAt E x).symm) =ᶠ[𝓝 (chartAt E x x)] fun _ => c := hf.comp_tendsto ht
  rw [he.fderiv_eq]
  have hz : fderiv ℝ (fun _ : E => c) (chartAt E x x) = 0 :=
    (hasFDerivAt_const c (chartAt E x x)).fderiv
  rw [hz]
  ext v
  rfl

theorem real_differential_zero_near_constant (f : C → ℝ) (x : C) (c : ℝ)
    (hf : f =ᶠ[𝓝 x] fun _ => c) :
    b3Forms_d (b3Forms_fun (E := E) f) =ᶠ[𝓝 x] 0 := by
  filter_upwards [hf.eventually_nhds] with y hy
  exact real_differential_zero_of_constant_germ f y c hy

end HodgeLean.Foundations.Curves.AbelTheorem
