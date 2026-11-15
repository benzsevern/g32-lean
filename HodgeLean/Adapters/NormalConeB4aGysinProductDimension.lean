import HodgeLean.Adapters.NormalConeB4aGysinAnalyticDimension

noncomputable section
namespace HodgeLean.Adapters

/-- Finite fibres bound an analytic source dimension by the total dimension of
a product of parameter and normal coordinate spaces. -/
theorem a3b4a_gysin_finite_fibre_product_dimension_le
    {d n c : ℕ} (U : Set (Fin d → ℂ)) (hU : IsOpen U) (hne : U.Nonempty)
    (f : (Fin d → ℂ) → ((Fin n → ℂ) × (Fin c → ℂ)))
    (hf : AnalyticOnNhd ℂ f U)
    (hfin : ∀ a, {z | z ∈ U ∧ f z = a}.Finite) : d ≤ n + c := by
  let L : ((Fin n → ℂ) × (Fin c → ℂ)) ≃L[ℂ] (Fin (n + c) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  apply a3b4a_gysin_finite_fibre_analytic_dimension_le U hU hne (fun z => L (f z))
  · intro z hz
    exact (L.analyticAt (f z)).comp (hf z hz)
  · intro a
    apply (hfin (L.symm a)).subset
    intro z hz
    refine ⟨hz.1, ?_⟩
    apply L.injective
    rw [hz.2, L.apply_symm_apply]

end HodgeLean.Adapters
