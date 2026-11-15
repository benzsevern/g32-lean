import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceFibreParam

/-! # Inverse regularity at points of injective derivative

Route: split the injective derivative by a complex linear projection. The
projected map has an invertible derivative, so the inverse function theorem
supplies an analytic left inverse. The local homeomorphism identifies this
left inverse with its given inverse near the image point.
-/
noncomputable section
namespace HodgeLean.Adapters
open Set Filter Topology
open scoped ContDiff

/-- An analytic local homeomorphism with injective derivative has an analytic
inverse germ, without assuming equal dimensions in advance. -/
theorem a3b4a_classAnalyticInverse_of_injective_derivative
    {n m : ℕ} (e : OpenPartialHomeomorph (Fin n → ℂ) (Fin m → ℂ))
    (x : Fin n → ℂ) (hx : x ∈ e.source) (ha : AnalyticAt ℂ e x)
    (hinj : Function.Injective (fderiv ℂ e x)) :
    AnalyticAt ℂ e.symm (e x) := by
  obtain ⟨L₀, hL₀⟩ := (fderiv ℂ e x : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let L : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ) := L₀.toContinuousLinearMap
  have hL : L ∘L fderiv ℂ e x = ContinuousLinearMap.id ℂ (Fin n → ℂ) := by
    ext1 v
    exact congrArg (fun T : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) => T v) hL₀
  let f : (Fin n → ℂ) → (Fin n → ℂ) := fun v => L (e v)
  have hf : AnalyticAt ℂ f x := (L.analyticAt (e x)).comp ha
  have hfd : HasFDerivAt f
      (ContinuousLinearEquiv.refl ℂ (Fin n → ℂ) : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) x := by
    have h := L.hasFDerivAt.comp x ha.differentiableAt.hasFDerivAt
    rw [hL] at h
    exact h
  have hfc : ContDiffAt ℂ ω f x := hf.contDiffAt
  let g := hfc.toOpenPartialHomeomorph f hfd (by simp)
  have hxg : x ∈ g.source := hfc.mem_toOpenPartialHomeomorph_source hfd (by simp)
  have hgcoe : (g : (Fin n → ℂ) → (Fin n → ℂ)) = f := rfl
  have hga : AnalyticAt ℂ g x := hf
  have hgd : fderiv ℂ g x =
      (ContinuousLinearEquiv.refl ℂ (Fin n → ℂ) : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :=
    hfd.fderiv
  have hgi := g.analyticAt_symm' hxg hga hgd
  change AnalyticAt ℂ g.symm (L (e x)) at hgi
  have hbase : AnalyticAt ℂ (fun y => g.symm (L y)) (e x) := by
    exact hgi.comp (L.analyticAt (e x))
  apply hbase.congr
  have htarget := e.open_target.mem_nhds (e.map_source hx)
  have hsource : ∀ᶠ y in 𝓝 (e x), e.symm y ∈ g.source := by
    apply (e.continuousAt_symm (e.map_source hx)).eventually
    rw [e.left_inv hx]
    exact g.open_source.mem_nhds hxg
  filter_upwards [htarget, hsource] with y hy hgy
  have heq : L y = g (e.symm y) := by
    change L y = L (e (e.symm y))
    rw [e.right_inv hy]
  rw [heq, g.left_inv hgy]

end HodgeLean.Adapters
