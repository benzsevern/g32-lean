import HodgeLean.Adapters.NormalConeB4aGysinRegularGraph

noncomputable section
namespace HodgeLean.Adapters

/-- The regular parameter graph can be chosen inside any prescribed open
neighborhood of its original source point. -/
theorem a3b4a_gysin_regular_graph_inside_open
    {n c : ℕ} (h : (Fin n → ℂ) → ((Fin n → ℂ) × (Fin c → ℂ)))
    (x : Fin n → ℂ) (hh : AnalyticAt ℂ h x)
    (hp : IsUnit (fderiv ℂ (fun z => (h z).1) x))
    (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ (E : OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ))
      (ψ : C((Fin n → ℂ), (Fin c → ℂ))),
      x ∈ E.source ∧ E.source ⊆ U ∧ (∀ z, E z = (h z).1) ∧
      AnalyticOnNhd ℂ ψ E.target ∧
      h '' E.source = {p | p.1 ∈ E.target ∧ p.2 = ψ p.1} := by
  obtain ⟨E₀, ψ, hx₀, hcoord₀, hψ, himage₀⟩ :=
    a3b4a_gysin_regular_parametrization_continuous_graph h x hh hp
  let E := E₀.restrOpen U hU
  have htarget : E.target ⊆ E₀.target := by
    intro b hb
    have hz := E.map_target hb
    have heq : E₀ (E.symm b) = b := E.right_inv hb
    rw [← heq]
    exact E₀.map_source hz.1
  have hgraph : ∀ z ∈ E.source, h z = (E z, ψ (E z)) := by
    intro z hz
    have hzg : h z ∈ h '' E₀.source := ⟨z, hz.1, rfl⟩
    rw [himage₀] at hzg
    apply Prod.ext
    · exact (hcoord₀ z).symm
    · change (h z).2 = ψ (E₀ z)
      rw [hcoord₀]
      exact hzg.2
  refine ⟨E, ψ, ⟨hx₀, hxU⟩, fun _ hz => hz.2,
    hcoord₀, hψ.mono htarget, ?_⟩
  exact a3b4a_gysin_parametrized_graph_image E h ψ hgraph

end HodgeLean.Adapters
