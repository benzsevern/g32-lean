import HodgeLean.Foundations.Program.CoverDictionaryEquivariance

/-! Rational vectors for equivariant holomorphic families. -/

noncomputable section
open Set Metric Filter Matrix Manifold
open scoped Topology ContDiff
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

variable {p : Fin 12 → ℂ} {O : b65p_Outputs p} {g : Fin 13 → b4b_Group}
  {D : b65z_SharedFamily (b65z_centre p) g} (S : b65g_Solutions p O D)

/-- On a common disc both equivariant holomorphic form spaces have rational representations. -/
theorem b65g_rational_representations_near :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ S.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
      (∀ φ ∈ b65g_homG D t S.conj, ∃ r : Fin 4 → RatFunc ℂ,
        (∀ i s, (r i).denom.eval s = 0 → s ∈ Set.range (b65p_poles p θ)) ∧
        b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11)
          (b65p_poles p θ) (b65g_Y S θ t) r φ) ∧
      (∀ ψ ∈ b65g_homG D t (!S.conj), ∃ q : Fin 4 → RatFunc ℂ,
        (∀ i s, (q i).denom.eval s = 0 → s ∈ Set.range (b65p_poles p θ)) ∧
        b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11)
          (b65p_poles p θ) (b65g_Y S θ t) q ψ) := by
  obtain ⟨ε, hε, hεS, hYm⟩ := b65g_Y_meromorphic_near S
  refine ⟨ε, hε, hεS, fun θ hθ t ht ↦ ?_⟩
  have hθS : θ ∈ ball (0 : ℂ) S.radius := ball_subset_ball hεS hθ
  constructor
  · intro φ hφ
    exact b65g_rational_rRepresents S θ hθS t ht φ hφ.1 (hYm θ hθ t ht)
      (b65g_r_coefficient_invariant S θ hθS t ht φ hφ)
  · intro ψ hψ
    exact b65g_rational_qRepresents S θ hθS t ht ψ hψ.1 (hYm θ hθ t ht)
      (b65g_q_coefficient_invariant S θ hθS t ht ψ hψ)

end HodgeLean.Foundations.Program
