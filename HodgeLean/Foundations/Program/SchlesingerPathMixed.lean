import HodgeLean.Foundations.Program.SchlesingerPathJoint
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65p_partial_first_hasDerivAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ × ℂ → E) (x y : ℂ) (hf : AnalyticAt ℂ f (x, y)) :
    HasDerivAt (fun z ↦ f (z, y)) (fderiv ℂ f (x, y) (1, 0)) x := by
  exact hf.differentiableAt.hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))

theorem b65p_partial_second_hasDerivAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ × ℂ → E) (x y : ℂ) (hf : AnalyticAt ℂ f (x, y)) :
    HasDerivAt (fun z ↦ f (x, z)) (fderiv ℂ f (x, y) (0, 1)) y := by
  exact hf.differentiableAt.hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))

theorem b65p_mixed_deriv_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℂ × ℂ → E) (x y : ℂ) (hf : AnalyticAt ℂ f (x, y)) :
    deriv (fun z ↦ deriv (fun w ↦ f (w, z)) x) y =
      deriv (fun w ↦ deriv (fun z ↦ f (w, z)) y) x := by
  have hfst : HasDerivAt (fun z ↦ (fderiv ℂ f (x, z)) (1, 0))
      (fderiv ℂ (fderiv ℂ f) (x, y) (0, 1) (1, 0)) y := by
    simpa using (b65p_partial_second_hasDerivAt (fderiv ℂ f) x y hf.fderiv).clm_apply
      (hasDerivAt_const y (1, 0))
  have hsnd : HasDerivAt (fun w ↦ (fderiv ℂ f (w, y)) (0, 1))
      (fderiv ℂ (fderiv ℂ f) (x, y) (1, 0) (0, 1)) x := by
    simpa using (b65p_partial_first_hasDerivAt (fderiv ℂ f) x y hf.fderiv).clm_apply
      (hasDerivAt_const x (0, 1))
  have hy : ∀ᶠ z in 𝓝 y, AnalyticAt ℂ f (x, z) :=
    ((continuousAt_const.prodMk continuousAt_id).tendsto).eventually hf.eventually_analyticAt
  have hx : ∀ᶠ w in 𝓝 x, AnalyticAt ℂ f (w, y) :=
    ((continuousAt_id.prodMk continuousAt_const).tendsto).eventually hf.eventually_analyticAt
  have he1 : (fun z ↦ deriv (fun w ↦ f (w, z)) x) =ᶠ[𝓝 y]
      (fun z ↦ (fderiv ℂ f (x, z)) (1, 0)) :=
    hy.mono (fun z hz ↦ (b65p_partial_first_hasDerivAt f x z hz).deriv)
  have he2 : (fun w ↦ deriv (fun z ↦ f (w, z)) y) =ᶠ[𝓝 x]
      (fun w ↦ (fderiv ℂ f (w, y)) (0, 1)) :=
    hx.mono (fun w hw ↦ (b65p_partial_second_hasDerivAt f w y hw).deriv)
  rw [he1.deriv_eq, he2.deriv_eq, hfst.deriv, hsnd.deriv]
  exact (show ContDiffAt ℂ 2 f (x, y) from hf.contDiffAt).isSymmSndFDerivAt
    (by simp) (0, 1) (1, 0)

theorem b65p_mixed_first_hasDerivAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℂ × ℂ → E) (x y : ℂ) (hf : AnalyticAt ℂ f (x, y)) :
    HasDerivAt (fun z ↦ deriv (fun w ↦ f (w, z)) x)
      (deriv (fun w ↦ deriv (fun z ↦ f (w, z)) y) x) y := by
  have hd : HasDerivAt (fun z ↦ (fderiv ℂ f (x, z)) (1, 0))
      (fderiv ℂ (fderiv ℂ f) (x, y) (0, 1) (1, 0)) y := by
    simpa using (b65p_partial_second_hasDerivAt (fderiv ℂ f) x y hf.fderiv).clm_apply
      (hasDerivAt_const y (1, 0))
  have hy : ∀ᶠ z in 𝓝 y, AnalyticAt ℂ f (x, z) :=
    ((continuousAt_const.prodMk continuousAt_id).tendsto).eventually hf.eventually_analyticAt
  have he : (fun z ↦ deriv (fun w ↦ f (w, z)) x) =ᶠ[𝓝 y]
      (fun z ↦ (fderiv ℂ f (x, z)) (1, 0)) :=
    hy.mono (fun z hz ↦ (b65p_partial_first_hasDerivAt f x z hz).deriv)
  have hh := hd.congr_of_eventuallyEq he
  apply hh.congr_deriv
  rw [← hh.deriv, b65p_mixed_deriv_eq f x y hf]

theorem b65p_joint_vertical_mixed (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (S Y : ℂ × ℂ → E →L[ℂ] E) (U V : Set ℂ) (hU : IsOpen U)
    (hY : AnalyticOnNhd ℂ Y (U ×ˢ V))
    (hODE : ∀ p ∈ U, ∀ θ ∈ V,
      HasDerivAt (fun z ↦ Y (p, z)) (S (p, θ) * Y (p, θ)) θ)
    (p θ : ℂ) (hp : p ∈ U) (hθ : θ ∈ V) (D : E →L[ℂ] E)
    (hS : HasDerivAt (fun q ↦ S (q, θ)) D p) :
    HasDerivAt (fun z ↦ deriv (fun q ↦ Y (q, z)) p)
      (D * Y (p, θ) + S (p, θ) * deriv (fun q ↦ Y (q, θ)) p) θ := by
  have hf := hY (p, θ) ⟨hp, hθ⟩
  have he : (fun q ↦ deriv (fun z ↦ Y (q, z)) θ) =ᶠ[𝓝 p]
      (fun q ↦ S (q, θ) * Y (q, θ)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact (hODE q hq θ hθ).deriv
  apply (b65p_mixed_first_hasDerivAt Y p θ hf).congr_deriv
  rw [he.deriv_eq]
  rw [deriv_fun_mul hS.differentiableAt
    (b65p_partial_first_hasDerivAt Y p θ hf).differentiableAt, hS.deriv]

theorem b65p_joint_flat_gauge (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (S H D Y : ℂ × ℂ → E →L[ℂ] E) (U : Set ℂ) (hU : IsOpen U)
    (r : ℝ) (hr : 0 < r) (hYa : AnalyticOnNhd ℂ Y (U ×ˢ ball 0 r))
    (hY0 : ∀ p ∈ U, Y (p, 0) = 1)
    (hSa : ∀ p ∈ U, AnalyticOnNhd ℂ (fun z ↦ S (p, z)) (ball 0 r))
    (hY : ∀ p ∈ U, ∀ θ ∈ ball (0 : ℂ) r,
      HasDerivAt (fun z ↦ Y (p, z)) (S (p, θ) * Y (p, θ)) θ)
    (hH : ∀ p ∈ U, ∀ θ ∈ ball (0 : ℂ) r,
      HasDerivAt (fun z ↦ H (p, z))
        (D (p, θ) + S (p, θ) * H (p, θ) - H (p, θ) * S (p, θ)) θ)
    (hS : ∀ p ∈ U, ∀ θ ∈ ball (0 : ℂ) r,
      HasDerivAt (fun q ↦ S (q, θ)) (D (p, θ)) p) :
    ∀ p ∈ U, ∀ θ ∈ ball (0 : ℂ) r,
      HasDerivAt (fun q ↦ Y (q, θ))
        (H (p, θ) * Y (p, θ) - Y (p, θ) * H (p, 0)) p := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  intro p hp θ hθ
  let W : ℂ → E →L[ℂ] E := fun z ↦ deriv (fun q ↦ Y (q, z)) p
  have hW0 : W 0 = 0 := by
    have he : (fun q ↦ Y (q, 0)) =ᶠ[𝓝 p] (fun _ ↦ (1 : E →L[ℂ] E)) := by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact hY0 q hq
    dsimp [W]
    rw [he.deriv_eq]
    exact deriv_const p 1
  have hW (z : ℂ) (hz : z ∈ ball (0 : ℂ) r) :
      HasDerivAt W (D (p, z) * Y (p, z) + S (p, z) * W z) z :=
    b65p_joint_vertical_mixed E S Y U (ball 0 r) hU hYa hY p z hp hz _ (hS p hp z hz)
  have he := b65p_flat_gauge_compatibility E r hr
    (fun z ↦ S (p, z)) (fun z ↦ H (p, z)) (fun z ↦ D (p, z))
    (fun z ↦ Y (p, z)) W (hSa p hp) (hY0 p hp) hW0 (hH p hp) (hY p hp) hW
  have hd := b65p_partial_first_hasDerivAt Y p θ (hYa (p, θ) ⟨hp, hθ⟩)
  exact hd.congr_deriv (hd.deriv.symm.trans (he θ hθ))

end HodgeLean.Foundations.Program
