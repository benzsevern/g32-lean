import HodgeLean.Foundations.Program.G32Native.PositiveMetricNormalTransport

/-! # Linearity of the uniquely specified metric normal representative

The linear map below retains the quotient equation and original kernel.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.TubularEuler

/-- The uniquely orthogonal quotient representatives form a real linear map.
Source: Lee, Introduction to Smooth Manifolds, second edition, normal spaces
in Theorem 6.24; uniqueness in `positiveMetric_normal_vector_exists_unique`.
For example, evaluation of this map is the same vector used in
`positiveMetricRepresentative_transport`.
HC no distance; AV milestone no distance. -/
def positiveMetricRepresentativeLinearMap
    {E N : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup N] [Module ℝ N]
    (G : LinearMap.BilinForm ℝ E) (hsym : ∀ u v, G u v = G v u)
    (hpos : ∀ u, u ≠ 0 → 0 < G u u)
    (T : E →ₗ[ℝ] N) (hT : Function.Surjective T) : N →ₗ[ℝ] E where
  toFun := positiveMetricRepresentative G hsym hpos T hT
  map_add' n m := by
    have hn := positiveMetricRepresentative_spec G hsym hpos T hT n
    have hm := positiveMetricRepresentative_spec G hsym hpos T hT m
    apply ((positiveMetric_normal_vector_exists_unique G hsym hpos T hT (n + m)).choose_spec.2
      (positiveMetricRepresentative G hsym hpos T hT n +
        positiveMetricRepresentative G hsym hpos T hT m) ?_).symm
    refine ⟨by rw [map_add, hn.1, hm.1], ?_⟩
    intro w hw
    rw [map_add, LinearMap.add_apply, hn.2 w hw, hm.2 w hw, add_zero]
  map_smul' r n := by
    have hn := positiveMetricRepresentative_spec G hsym hpos T hT n
    apply ((positiveMetric_normal_vector_exists_unique G hsym hpos T hT (r • n)).choose_spec.2
      (r • positiveMetricRepresentative G hsym hpos T hT n) ?_).symm
    refine ⟨by rw [map_smul, hn.1], ?_⟩
    intro w hw
    rw [map_smul, LinearMap.smul_apply, hn.2 w hw, smul_zero]

#print axioms positiveMetricRepresentativeLinearMap

end HodgeLean.Foundations.TubularEuler
