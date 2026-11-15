import HodgeLean.Adapters.NormalConeB4aGysinGraphChart

noncomputable section
namespace HodgeLean.Adapters
open scoped Topology

/-- Agreement on a normal ball transports derivatives at every interior point
to the globally defined disk family. -/
theorem a3b4a_gysin_disk_family_derivative
    {Y : Type*} [TopologicalSpace Y] {n c d : ℕ}
    (Φ : OpenPartialHomeomorph Y ((Fin n → ℂ) × (Fin c → ℂ)))
    (F : C(((Fin n → ℂ) × (Fin c → ℂ)), Y))
    (ρ : ℝ) (a : Fin n → ℂ) (v : Fin c → ℂ)
    (hv : v ∈ Metric.ball 0 ρ)
    (hF : ∀ u ∈ Metric.closedBall 0 ρ, F (a, u) = Φ.symm (a, u))
    (G : Y → (Fin d → ℂ)) (L : (Fin c → ℂ) →L[ℂ] (Fin d → ℂ))
    (hL : HasFDerivAt (fun u => G (Φ.symm (a, u + v))) L 0) :
    HasFDerivAt (fun u => G (F (a, u + v))) L 0 := by
  have hnear : ∀ᶠ u : Fin c → ℂ in 𝓝 0, u + v ∈ Metric.ball 0 ρ := by
    exact (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds
      (by simpa using Metric.isOpen_ball.mem_nhds hv)
  apply hL.congr_of_eventuallyEq
  filter_upwards [hnear] with u hu
  rw [hF (u + v) (Metric.ball_subset_closedBall hu)]

end HodgeLean.Adapters
