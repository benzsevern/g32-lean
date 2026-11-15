import HodgeLean.Foundations.AnalyticAlbanese.PeriodLift

/-! # Linear representation of holomorphic additive maps

HC no distance; AV milestone no distance.
-/
set_option maxHeartbeats 200000
noncomputable section
open Manifold Filter Topology
open scoped TensorProduct ContDiff
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.AnalyticAlbanese
attribute [local instance] b2_torus_isManifold

variable {Λ Μ : Type} [AddCommGroup Λ] [Module.Finite ℤ Λ]
  [AddCommGroup Μ] [Module.Finite ℤ Μ]
  (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (G : Submodule ℂ (ℂ ⊗[ℤ] Μ))
  [DiscreteTopology (b2_latticeMap Λ F).range] [DiscreteTopology (b2_latticeMap Μ G).range]
  [CompactSpace (b2_torus Λ F)] [ConnectedSpace (b2_torus Λ F)]
  (H : b2_torus Λ F →+ b2_torus Μ G)
  (hH : ContMDiff 𝓘(ℂ, b5_V Λ F) 𝓘(ℂ, b5_V Μ G) ω H)

/-- The linear representation in the original quotient covering spaces.
HC no distance; AV milestone no distance. -/
def analyticLinear : ((ℂ ⊗[ℤ] Λ) ⧸ F) →ₗ[ℂ] ((ℂ ⊗[ℤ] Μ) ⧸ G) :=
  (b2_coord _).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun i ↦ b3A_formFunctional F (pulledCoordinate G H hH i)) ∘ₗ
      (b2_coord _).toLinearMap

/-- On representatives, a holomorphic additive map is its linear representation.
HC no distance; AV milestone no distance. -/
theorem analyticLinear_mk (w : (ℂ ⊗[ℤ] Λ) ⧸ F) :
    H (QuotientAddGroup.mk w) = QuotientAddGroup.mk (analyticLinear F G H hH w) := by
  let γ : ℝ → b2_torus Λ F := fun u ↦ QuotientAddGroup.mk ((u : ℂ) • w + 0)
  have hγ := (b3A_torusLine F w 0).1
  have hc := b3A_contMDiff_comp_real H hH γ hγ
  have hv : ∀ t, b3A_vel (E := b5_V Μ G) (C := b2_torus Μ G) (H ∘ γ) t =
      b2_coord _ (analyticLinear F G H hH w) := by
    intro t
    simp only [analyticLinear, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    ext i
    rw [show b3A_vel (E := b5_V Μ G) (C := b2_torus Μ G) (H ∘ γ) t =
      mfderiv 𝓘(ℂ, b5_V Λ F) 𝓘(ℂ, b5_V Μ G) H (γ t)
        (b3_velocity (b5_V Λ F) (b2_torus Λ F) γ t) from b3A_velocity_comp H hH γ hγ t]
    rw [(b3A_torusLine F w 0).2 t]
    exact b3A_torus_form_apply F (pulledCoordinate G H hH i)
      (pulledCoordinate G H hH i).2 (γ t) (b2_coord _ w)
  have he := b3A_torus_develop G (H ∘ γ) hc 1
  have hzero : γ 0 = 0 := by simp only [γ, Complex.ofReal_zero, zero_smul, add_zero]; rfl
  have hone : γ 1 = QuotientAddGroup.mk w := by
    simp only [γ, Complex.ofReal_one, one_smul, add_zero]
  change H (γ 1) = H (γ 0) + _ at he
  rw [hone, hzero, map_zero, zero_add] at he
  rw [he]
  congr 1
  simp only [hv, intervalIntegral.integral_const, sub_zero, one_smul,
    LinearEquiv.symm_apply_apply]

end HodgeLean.Foundations.AnalyticAlbanese
