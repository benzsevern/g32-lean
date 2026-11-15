import HodgeLean.Adapters.NormalConeB4aGysinParametrizedGraph
import HodgeLean.Adapters.NormalConeB4aGysinAnalyticExtension

noncomputable section
namespace HodgeLean.Adapters

/-- A regular analytic parameter projection supplies a graph over an open
parameter target, with a global continuous graph function analytic there. -/
theorem a3b4a_gysin_regular_parametrization_continuous_graph
    {n c : ℕ} (h : (Fin n → ℂ) → ((Fin n → ℂ) × (Fin c → ℂ)))
    (x : Fin n → ℂ) (hh : AnalyticAt ℂ h x)
    (hp : IsUnit (fderiv ℂ (fun z => (h z).1) x)) :
    ∃ (E : OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ))
      (ψ : C((Fin n → ℂ), (Fin c → ℂ))),
      x ∈ E.source ∧ (∀ z, E z = (h z).1) ∧ AnalyticOnNhd ℂ ψ E.target ∧
      h '' E.source = {p | p.1 ∈ E.target ∧ p.2 = ψ p.1} := by
  obtain ⟨E₀, ψ₀, hx₀, hcoord₀, _, hψ₀, hgraph₀⟩ :=
    a3b4a_gysin_regular_parametrization_graph h x hh hp
  obtain ⟨ψ, U, hU, haU, hfix, hψ⟩ :=
    a3b4a_gysin_analytic_germ_continuous_extension ψ₀ (h x).1 hψ₀
  let W := E₀.source ∩ E₀ ⁻¹' U
  have hW : IsOpen W := E₀.isOpen_inter_preimage hU
  let E := E₀.restrOpen W hW
  have hx : x ∈ E.source := by
    refine ⟨hx₀, hx₀, ?_⟩
    change E₀ x ∈ U
    rw [hcoord₀]
    exact haU
  have htarget : E.target ⊆ U := by
    intro b hb
    have hz := E.map_target hb
    have hzU : E₀ (E.symm b) ∈ U := hz.2.2
    have heq : E₀ (E.symm b) = b := E.right_inv hb
    rwa [heq] at hzU
  have hgraph : ∀ z ∈ E.source, h z = (E z, ψ (E z)) := by
    intro z hz
    have heq := hgraph₀ z hz.1
    rw [← hfix (E₀ z) hz.2.2] at heq
    exact heq
  refine ⟨E, ψ, hx, hcoord₀, hψ.mono htarget, ?_⟩
  exact a3b4a_gysin_parametrized_graph_image E h ψ hgraph

end HodgeLean.Adapters
