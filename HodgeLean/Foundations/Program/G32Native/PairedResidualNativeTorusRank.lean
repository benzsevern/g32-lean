import HodgeLean.Foundations.Program.G32Native.PairedResidualTorusChartLift
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Native covering rank and the original torus-valued manifold differential -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open scoped TensorProduct Topology Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- A native-chart covering lift with surjective derivative gives a surjective
manifold differential of the original torus-valued map.
Source: Forster, Lectures on Riemann Surfaces, §21; manifold chain rule. -/
theorem residual_native_cover_mfderiv_surjective
    (X : Over (Spec ↧ℂ)) (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    {L : Type} [AddCommGroup L] [Module.Finite ℤ L]
    (F : Submodule ℂ (ℂ ⊗[ℤ] L)) [DiscreteTopology (b2_latticeMap L F).range]
    (s : ComplexPoint X → b2_torus L F)
    (hs : ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, b5_V L F) ω s)
    (x : ComplexPoint X) (g : (Fin n → ℂ) → b5_V L F)
    (hg : AnalyticAt ℂ g (localChart X n x x))
    (he : ∀ᶠ w in 𝓝 x, b2_torusCover L F (g (localChart X n x w)) = s w)
    (hr : Function.Surjective (fderiv ℂ g (localChart X n x x))) :
    Function.Surjective (mfderiv 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, b5_V L F) s x) := by
  let C := localChart X n x
  have hx : x ∈ C.source := mem_localChart_source _ _ _
  have ht : C x ∈ C.target := C.map_source hx
  have hi : C.symm (C x) = x := C.left_inv hx
  have hCi : ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω C.symm (C x) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) ht
  have hct : Tendsto C.symm (𝓝 (C x)) (𝓝 x) := by
    have hh := (C.symm.continuousAt ht).tendsto
    rw [hi] at hh
    exact hh
  have hcover : s ∘ C.symm =ᶠ[𝓝 (C x)] b2_torusCover L F ∘ g := by
    filter_upwards [hct.eventually he, C.open_target.mem_nhds ht] with u hu hut
    change b2_torusCover L F (g (C (C.symm u))) = s (C.symm u) at hu
    change s (C.symm u) = b2_torusCover L F (g u)
    simpa only [C.right_inv hut] using hu.symm
  have hderiv : mfderiv 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, b5_V L F) (s ∘ C.symm) (C x) =
      fderiv ℂ g (C x) :=
    (torusCover_lift_mfderiv F (s ∘ C.symm) g (C x)
      hg.differentiableAt.mdifferentiableAt hcover).trans mfderiv_eq_fderiv
  have hsurj : Function.Surjective
      (mfderiv 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, b5_V L F) (s ∘ C.symm) (C x)) := by
    rw [hderiv]
    exact hr
  have hsd : MDifferentiableAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, b5_V L F) s (C.symm (C x)) :=
    hi.symm ▸ hs.mdifferentiable (by simp) x
  have hc := mfderiv_comp (C x) hsd (hCi.mdifferentiableAt (by simp))
  rw [hi] at hc
  intro y
  obtain ⟨v, hv⟩ := hsurj y
  refine ⟨mfderiv 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) C.symm (C x) v, ?_⟩
  exact (congrArg (fun A => A v) hc).symm.trans hv

#print axioms residual_native_cover_mfderiv_surjective
end HodgeLean.Foundations.Program.G32Native
