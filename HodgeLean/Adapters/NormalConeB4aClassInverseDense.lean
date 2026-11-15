import HodgeLean.Adapters.NormalConeB4aClassInverseRegular

/-! # Dense regular inverse germs of analytic charts

Route: injectivity gives finite fibres on every open neighborhood. The
analytic rank theorem supplies an injective derivative somewhere in each
such neighborhood; inverse regularity then applies at that point.
-/
noncomputable section
namespace HodgeLean.Adapters
open Set Filter Topology
open HodgeLean.Foundations.Analytic

/-- Every nonempty open subset of an analytic chart source contains a point
where the derivative is injective and the inverse germ is analytic. -/
theorem a3b4a_classAnalyticInverse_exists_regular
    {n m : ℕ} (e : OpenPartialHomeomorph (Fin n → ℂ) (Fin m → ℂ))
    (ha : AnalyticOnNhd ℂ e e.source)
    (V : Set (Fin n → ℂ)) (hV : IsOpen V) (hne : V.Nonempty) (hVS : V ⊆ e.source) :
    ∃ x ∈ V, Function.Injective (fderiv ℂ e x) ∧ AnalyticAt ℂ e.symm (e x) := by
  have hfin (w : Fin m → ℂ) : {v | v ∈ V ∧ e v = w}.Finite := by
    apply Set.Subsingleton.finite
    intro u hu v hv
    exact e.injOn (hVS hu.1) (hVS hv.1) (hu.2.trans hv.2.symm)
  obtain ⟨x, hx, hinj⟩ := ancrs_exists_injective_of_finite_fibres hV hne
    (ha.mono hVS) hfin
  exact ⟨x, hx, hinj, a3b4a_classAnalyticInverse_of_injective_derivative
    e x (hVS hx) (ha x (hVS hx)) hinj⟩

end HodgeLean.Adapters
