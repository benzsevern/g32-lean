import HodgeLean.Adapters.NormalConeB4aClassInverseDense

/-! # Dimension equality for analytic charts

Route: choose a point with analytic inverse germ using the finite-fibre rank
theorem. Differentiating the two local inverse identities gives mutually
inverse linear derivatives and equality of the complex dimensions.
-/
noncomputable section
namespace HodgeLean.Adapters
open Set Filter Topology

/-- A nonempty analytic local homeomorphism between complex coordinate spaces
has equal source and target dimensions. -/
theorem a3b4a_classAnalyticChart_dimensions
    {n m : ℕ} (e : OpenPartialHomeomorph (Fin n → ℂ) (Fin m → ℂ))
    (ha : AnalyticOnNhd ℂ e e.source) (hne : e.source.Nonempty) : n = m := by
  obtain ⟨x, hx, hinj, hi⟩ := a3b4a_classAnalyticInverse_exists_regular
    e ha e.source e.open_source hne (Subset.rfl)
  have hdn : n ≤ m := by
    simpa only [Module.finrank_fin_fun] using
      LinearMap.finrank_le_finrank_of_injective
        (f := (fderiv ℂ e x : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ))) hinj
  have hd : HasFDerivAt e (fderiv ℂ e x) (e.symm (e x)) := by
    rw [e.left_inv hx]
    exact (ha x hx).differentiableAt.hasFDerivAt
  have hcomp := hd.comp (e x) hi.differentiableAt.hasFDerivAt
  have heq : (fderiv ℂ e x).comp (fderiv ℂ e.symm (e x)) =
      ContinuousLinearMap.id ℂ (Fin m → ℂ) := by
    rw [← hcomp.fderiv]
    have hl : (e ∘ e.symm) =ᶠ[𝓝 (e x)] id := by
      filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with y hy
      exact e.right_inv hy
    simpa only [fderiv_id] using hl.fderiv_eq (𝕜 := ℂ)
  have hinv : Function.Injective (fderiv ℂ e.symm (e x)) := by
    have hl : Function.LeftInverse (fderiv ℂ e x) (fderiv ℂ e.symm (e x)) :=
      fun v => congrArg (fun L : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ) => L v) heq
    exact hl.injective
  have hdm : m ≤ n := by
    simpa only [Module.finrank_fin_fun] using
      LinearMap.finrank_le_finrank_of_injective
        (f := (fderiv ℂ e.symm (e x) : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ))) hinv
  exact Nat.le_antisymm hdn hdm

end HodgeLean.Adapters
