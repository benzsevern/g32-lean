import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic

noncomputable section
open Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b52_three_term_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → ℂ) {U : Set E} (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (k : E) (C : ℂ)
    (hsum : ∀ x ∈ U, ∀ y ∈ U, k - x - y ∈ U → g x + g y + g (k - x - y) = C)
    (b t : E) (hb : b ∈ U) (ht : t ∈ U) (hbt : k - t - b ∈ U) :
    fderiv ℂ g t = fderiv ℂ g b := by
  let x := k - t - b
  have hxt : k - x - b = t := by dsimp [x]; abel
  have hn : {y : E | y ∈ U ∧ k - x - y ∈ U} ∈ 𝓝 b :=
    (hU.inter (hU.preimage (continuous_const.sub continuous_id))).mem_nhds
      ⟨hb, by change k - x - b ∈ U; rwa [hxt]⟩
  have he : (fun y ↦ g x + g y + g (k - x - y)) =ᶠ[𝓝 b] (fun _ ↦ C) := by
    filter_upwards [hn] with y hy
    exact hsum x hbt y hy.1 hy.2
  have hb' := hg.differentiableAt (hU.mem_nhds hb)
  have ht' := hg.differentiableAt (hU.mem_nhds (show k - x - b ∈ U by rwa [hxt]))
  have hd := (hb'.hasFDerivAt.const_add (g x)).add
    (ht'.hasFDerivAt.comp b ((hasFDerivAt_const (k - x) b).sub (hasFDerivAt_id b)))
  simp only [Function.comp_def, id_eq, Pi.add_def] at hd
  have hz := hd.unique ((hasFDerivAt_const C b).congr_of_eventuallyEq he)
  ext v
  have hv := congrArg (fun A : E →L[ℂ] ℂ ↦ A v) hz
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.neg_apply, zero_sub, map_neg, hxt] at hv
  exact (eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hv)).symm

theorem b52_three_term_locally_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → ℂ) {U : Set E} (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (k : E) (C : ℂ)
    (hsum : ∀ x ∈ U, ∀ y ∈ U, k - x - y ∈ U → g x + g y + g (k - x - y) = C)
    (b t : E) (hb : b ∈ U) (ht : t ∈ U) (hbt : k - t - b ∈ U) :
    ∃ (L : E →L[ℂ] ℂ) (d : ℂ) (W : Set E),
      IsOpen W ∧ W.Nonempty ∧ W ⊆ U ∧ ∀ x ∈ W, g x = L x + d := by
  letI := NormedSpace.restrictScalars ℝ ℂ E
  have hopen : IsOpen (U ∩ {x | k - x - b ∈ U}) :=
    hU.inter (hU.preimage ((continuous_const.sub continuous_id).sub continuous_const))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen t ⟨ht, hbt⟩
  let L := fderiv ℂ g b
  have hd : (Metric.ball t r).EqOn (fderiv ℂ g) (fderiv ℂ L) := by
    intro x hx
    rw [L.fderiv]
    exact b52_three_term_fderiv g hU hg k C hsum b x hb
      (hball hx).1 (hball hx).2
  obtain ⟨d, hd⟩ := Metric.isOpen_ball.exists_eq_add_of_fderiv_eq
    (convex_ball t r).isPreconnected (hg.mono fun x hx ↦ (hball hx).1)
    L.differentiable.differentiableOn hd
  exact ⟨L, d, Metric.ball t r, Metric.isOpen_ball, ⟨t, Metric.mem_ball_self hr⟩,
    (fun x hx ↦ (hball hx).1), hd⟩

end HodgeLean.Foundations.Program
