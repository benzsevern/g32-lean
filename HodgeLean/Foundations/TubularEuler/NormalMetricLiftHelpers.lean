import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach

/-! # Canonical normal lifts from a surjective differential

The Hermitian Gram operator constructs the lift without choosing a basis or a complement.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.TubularEuler

variable {𝕜 : Type*} [RCLike 𝕜]

variable {E N : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup N] [InnerProductSpace 𝕜 N] [CompleteSpace N]
variable [FiniteDimensional 𝕜 N]

theorem normalGram_bijective (D : E →L[𝕜] N) (hD : Function.Surjective D) :
    Function.Bijective (D.comp D.adjoint) := by
  have hk : D.adjoint.ker = ⊥ := by
    rw [← D.orthogonal_range, LinearMap.range_eq_top.mpr hD, Submodule.top_orthogonal_eq_bot]
  have hi : Function.Injective D.adjoint := LinearMap.ker_eq_bot.mp hk
  have hG : Function.Injective (D.comp D.adjoint) :=
    D.self_comp_adjoint_injective_iff.mpr hi
  exact ⟨hG, LinearMap.injective_iff_surjective.mp hG⟩

def normalMetricLift (D : E →L[𝕜] N) : N →L[𝕜] E :=
  D.adjoint.comp (ContinuousLinearMap.inverse (D.comp D.adjoint))

theorem normalMetricLift_rightInverse (D : E →L[𝕜] N) (hD : Function.Surjective D) :
    Function.RightInverse (normalMetricLift D) D := by
  let G := ContinuousLinearEquiv.ofBijective (D.comp D.adjoint)
    (LinearMap.ker_eq_bot.mpr (normalGram_bijective D hD).1)
    (LinearMap.range_eq_top.mpr (normalGram_bijective D hD).2)
  have hG : ContinuousLinearMap.inverse (D.comp D.adjoint) = G.symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv G
  intro n
  change D (D.adjoint (ContinuousLinearMap.inverse (D.comp D.adjoint) n)) = n
  rw [hG]
  exact G.apply_symm_apply n

theorem normalMetricLift_orthogonal (D : E →L[𝕜] N) (n : N) (w : E) (hw : D w = 0) :
    inner 𝕜 (normalMetricLift D n) w = 0 := by
  change inner 𝕜 (D.adjoint (ContinuousLinearMap.inverse (D.comp D.adjoint) n)) w = 0
  rw [D.adjoint_inner_left, hw, inner_zero_right]

theorem normalMetricLift_unique (D : E →L[𝕜] N) (hD : Function.Surjective D)
    (n : N) (z : E) (hz : D z = n)
    (hzorth : ∀ w, D w = 0 → inner 𝕜 z w = 0) : z = normalMetricLift D n := by
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := 𝕜)).mp
  have hd : D (z - normalMetricLift D n) = 0 := by
    rw [map_sub, hz, normalMetricLift_rightInverse D hD n, sub_self]
  rw [inner_sub_left, hzorth _ hd, normalMetricLift_orthogonal D n _ hd, sub_self]

theorem normalMetricLift_naturality (D D' : E →L[𝕜] N) (hD : Function.Surjective D)
    (U : E ≃ₗᵢ[𝕜] E) (V : N ≃L[𝕜] N)
    (hcompat : ∀ z, D' (U z) = V (D z)) (n : N) :
    normalMetricLift D' (V n) = U (normalMetricLift D n) := by
  have hD' : Function.Surjective D' := by
    intro y
    obtain ⟨z, hz⟩ := hD (V.symm y)
    refine ⟨U z, ?_⟩
    rw [hcompat, hz, V.apply_symm_apply]
  symm
  apply normalMetricLift_unique D' hD' (V n) (U (normalMetricLift D n))
  · rw [hcompat, normalMetricLift_rightInverse D hD n]
  · intro w hw
    have hk : D (U.symm w) = 0 := by
      apply V.injective
      rw [← hcompat, U.apply_symm_apply, hw, map_zero]
    have hi := U.inner_map_map (normalMetricLift D n) (U.symm w)
    rw [U.apply_symm_apply] at hi
    exact hi.trans (normalMetricLift_orthogonal D n (U.symm w) hk)

#print axioms normalMetricLift_naturality

#print axioms normalMetricLift_unique

#print axioms normalMetricLift_orthogonal

#print axioms normalMetricLift_rightInverse

#print axioms normalGram_bijective

end HodgeLean.Foundations.TubularEuler
