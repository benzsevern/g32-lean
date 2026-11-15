import HodgeLean.Foundations.Program.G32Native.PositiveMetricNormalVector

/-! # Metric normal representatives and change of coordinates

The representative is selected by the actual quotient equation and metric
orthogonality, which makes its value independent of coordinate choices.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.TubularEuler

variable {E N : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable [AddCommGroup N] [Module ℝ N]
variable (G : LinearMap.BilinForm ℝ E) (hsym : ∀ u v, G u v = G v u)
variable (hpos : ∀ u, u ≠ 0 → 0 < G u u)
variable (T : E →ₗ[ℝ] N) (hT : Function.Surjective T)

/-- The uniquely metric-orthogonal representative of the actual quotient value.
Source: `positiveMetric_normal_vector_exists_unique`.
For example, the coordinate-change equation in `positiveMetricRepresentative_transport`
identifies its value in two presentations of the same metric quotient.
HC no distance; AV milestone no distance. -/
def positiveMetricRepresentative (n : N) : E :=
  (positiveMetric_normal_vector_exists_unique G hsym hpos T hT n).choose

/-- The selected vector solves the original quotient equation and is orthogonal
to the original kernel.
Source: `positiveMetric_normal_vector_exists_unique`.
HC no distance; AV milestone no distance. -/
theorem positiveMetricRepresentative_spec (n : N) :
    T (positiveMetricRepresentative G hsym hpos T hT n) = n ∧
      ∀ w, T w = 0 → G (positiveMetricRepresentative G hsym hpos T hT n) w = 0 :=
  (positiveMetric_normal_vector_exists_unique G hsym hpos T hT n).choose_spec.1

#print axioms positiveMetricRepresentative_spec

/-- Simultaneous changes of tangent and quotient coordinates transport the
canonical vector through the tangent equivalence. The actual metric and
quotient equations, rather than an arbitrary splitting, fix the vector.
Source: uniqueness in `positiveMetric_normal_vector_exists_unique`;
Lee, Introduction to Smooth Manifolds, second edition, metric normal spaces.
HC no distance; AV milestone no distance. -/
theorem positiveMetricRepresentative_transport
    {E' N' : Type*} [AddCommGroup E'] [Module ℝ E'] [FiniteDimensional ℝ E']
    [AddCommGroup N'] [Module ℝ N']
    (G' : LinearMap.BilinForm ℝ E') (hsym' : ∀ u v, G' u v = G' v u)
    (hpos' : ∀ u, u ≠ 0 → 0 < G' u u)
    (T' : E' →ₗ[ℝ] N') (hT' : Function.Surjective T')
    (L : E ≃ₗ[ℝ] E') (V : N ≃ₗ[ℝ] N')
    (hmetric : ∀ u w, G' (L u) (L w) = G u w)
    (hcompat : ∀ u, T' (L u) = V (T u)) (n : N) :
    positiveMetricRepresentative G' hsym' hpos' T' hT' (V n) =
      L (positiveMetricRepresentative G hsym hpos T hT n) := by
  let v := positiveMetricRepresentative G hsym hpos T hT n
  have hv := positiveMetricRepresentative_spec G hsym hpos T hT n
  have hcand : T' (L v) = V n ∧ ∀ w, T' w = 0 → G' (L v) w = 0 := by
    refine ⟨?_, ?_⟩
    · rw [hcompat, hv.1]
    · intro w hw
      have hk : T (L.symm w) = 0 := by
        apply V.injective
        rw [← hcompat, L.apply_symm_apply, hw, map_zero]
      calc
        G' (L v) w = G' (L v) (L (L.symm w)) := by rw [L.apply_symm_apply]
        _ = G v (L.symm w) := hmetric _ _
        _ = 0 := hv.2 _ hk
  exact ((positiveMetric_normal_vector_exists_unique G' hsym' hpos' T' hT'
    (V n)).choose_spec.2 (L v) hcand).symm

#print axioms positiveMetricRepresentative_transport

end HodgeLean.Foundations.TubularEuler
