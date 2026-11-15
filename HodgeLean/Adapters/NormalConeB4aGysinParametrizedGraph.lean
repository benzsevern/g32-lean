import HodgeLean.Adapters.NormalConeB4aClassInverseRegular

noncomputable section
namespace HodgeLean.Adapters
open scoped Topology ContDiff

/-- An analytic parametrization with invertible parameter projection has a local
analytic graph over those parameters, through its original marked point. -/
theorem a3b4a_gysin_regular_parametrization_graph
    {n c : ℕ} (h : (Fin n → ℂ) → ((Fin n → ℂ) × (Fin c → ℂ)))
    (x : Fin n → ℂ) (hh : AnalyticAt ℂ h x)
    (hp : IsUnit (fderiv ℂ (fun z => (h z).1) x)) :
    ∃ (E : OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ))
      (ψ : (Fin n → ℂ) → (Fin c → ℂ)),
      x ∈ E.source ∧ (∀ z, E z = (h z).1) ∧
      AnalyticAt ℂ E.symm (h x).1 ∧ AnalyticAt ℂ ψ (h x).1 ∧
      ∀ z ∈ E.source, h z = (E z, ψ (E z)) := by
  let f : (Fin n → ℂ) → (Fin n → ℂ) := fun z => (h z).1
  have hf : AnalyticAt ℂ f x := (ContinuousLinearMap.fst ℂ
    (Fin n → ℂ) (Fin c → ℂ)).analyticAt (h x) |>.comp hh
  have hb := ContinuousLinearMap.isUnit_iff_bijective.mp hp
  let e : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearEquiv.ofBijective (fderiv ℂ f x)
      (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  have hfd : HasFDerivAt f (e : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) x :=
    hf.differentiableAt.hasFDerivAt
  have hfc : ContDiffAt ℂ ω f x := hf.contDiffAt
  let E := hfc.toOpenPartialHomeomorph f hfd (by simp)
  have hx : x ∈ E.source := hfc.mem_toOpenPartialHomeomorph_source hfd (by simp)
  have hi : AnalyticAt ℂ E.symm (h x).1 :=
    a3b4a_classAnalyticInverse_of_injective_derivative E x hx hf hb.1
  let ψ : (Fin n → ℂ) → (Fin c → ℂ) := fun a => (h (E.symm a)).2
  have hhi : AnalyticAt ℂ h (E.symm (h x).1) := by
    change AnalyticAt ℂ h (E.symm (E x))
    rw [E.left_inv hx]
    exact hh
  have hψ : AnalyticAt ℂ ψ (h x).1 :=
    ((ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin c → ℂ)).analyticAt _).comp (hhi.comp hi)
  refine ⟨E, ψ, hx, fun _ => rfl, hi, hψ, ?_⟩
  intro z hz
  change h z = (E z, (h (E.symm (E z))).2)
  rw [E.left_inv hz]
  rfl

/-- The image of a parametrized graph is exactly its graph over the parameter
chart target. -/
theorem a3b4a_gysin_parametrized_graph_image
    {n c : ℕ} (E : OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ))
    (h : (Fin n → ℂ) → ((Fin n → ℂ) × (Fin c → ℂ)))
    (ψ : (Fin n → ℂ) → (Fin c → ℂ))
    (hh : ∀ z ∈ E.source, h z = (E z, ψ (E z))) :
    h '' E.source = {p | p.1 ∈ E.target ∧ p.2 = ψ p.1} := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [hh z hz]
    exact ⟨E.map_source hz, rfl⟩
  · rintro ⟨hp, hgraph⟩
    refine ⟨E.symm p.1, E.map_target hp, ?_⟩
    rw [hh _ (E.map_target hp), E.right_inv hp]
    exact Prod.ext rfl hgraph.symm

end HodgeLean.Adapters
