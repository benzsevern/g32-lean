import HodgeLean.Foundations.TubularEuler.MetricConnectionCoefficientHelpers

/-! # Canonical normal lifting for a varying ambient metric

The inverse metric weights the transverse Gram operator in arbitrary Hilbert coordinates.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.TubularEuler

variable {E N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]
variable [NormedAddCommGroup N] [InnerProductSpace ℝ N] [CompleteSpace N]
variable [FiniteDimensional ℝ N]

theorem metricOperator_inverse_positive
    (G : E →L[ℝ] E) (hpos : ∀ u : E, u ≠ 0 → 0 < inner ℝ (G u) u)
    (w : E) (hw : w ≠ 0) : 0 < inner ℝ (ContinuousLinearMap.inverse G w) w := by
  have hGI := metricOperator_isInvertible_of_positive G hpos
  have hu : ContinuousLinearMap.inverse G w ≠ 0 := by
    intro hu
    have h := hGI.self_apply_inverse w
    rw [hu, map_zero] at h
    exact hw h.symm
  have h := hpos (ContinuousLinearMap.inverse G w) hu
  rw [hGI.self_apply_inverse, real_inner_comm (ContinuousLinearMap.inverse G w) w] at h
  exact h

def metricNormalGram (G : E →L[ℝ] E) (D : E →L[ℝ] N) : N →L[ℝ] N :=
  D.comp ((ContinuousLinearMap.inverse G).comp D.adjoint)

theorem metricNormalGram_bijective
    (G : E →L[ℝ] E) (hpos : ∀ u : E, u ≠ 0 → 0 < inner ℝ (G u) u)
    (D : E →L[ℝ] N) (hD : Function.Surjective D) : Function.Bijective (metricNormalGram G D) := by
  have hk : D.adjoint.ker = ⊥ := by
    rw [← D.orthogonal_range, LinearMap.range_eq_top.mpr hD, Submodule.top_orthogonal_eq_bot]
  have hAdj : Function.Injective D.adjoint := LinearMap.ker_eq_bot.mp hk
  have hz : ∀ n : N, metricNormalGram G D n = 0 → n = 0 := by
    intro n hn
    by_contra hne
    have hAn : D.adjoint n ≠ 0 := by
      intro h
      apply hne
      apply hAdj
      simpa only [map_zero] using h
    have h := metricOperator_inverse_positive G hpos (D.adjoint n) hAn
    change D (ContinuousLinearMap.inverse G (D.adjoint n)) = 0 at hn
    rw [D.adjoint_inner_right, hn, inner_zero_left] at h
    exact (lt_irrefl 0) h
  have hi : Function.Injective (metricNormalGram G D) := by
    intro u v huv
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub, huv, sub_self]
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

def metricNormalLift (G : E →L[ℝ] E) (D : E →L[ℝ] N) : N →L[ℝ] E :=
  (ContinuousLinearMap.inverse G).comp
    (D.adjoint.comp (ContinuousLinearMap.inverse (metricNormalGram G D)))

theorem metricNormalLift_rightInverse
    (G : E →L[ℝ] E) (hpos : ∀ u : E, u ≠ 0 → 0 < inner ℝ (G u) u)
    (D : E →L[ℝ] N) (hD : Function.Surjective D) :
    Function.RightInverse (metricNormalLift G D) D := by
  let e := ContinuousLinearEquiv.ofBijective (metricNormalGram G D)
    (LinearMap.ker_eq_bot.mpr (metricNormalGram_bijective G hpos D hD).1)
    (LinearMap.range_eq_top.mpr (metricNormalGram_bijective G hpos D hD).2)
  have hI : (metricNormalGram G D).IsInvertible := ⟨e, rfl⟩
  intro n
  change metricNormalGram G D (ContinuousLinearMap.inverse (metricNormalGram G D) n) = n
  exact hI.self_apply_inverse n

theorem metricNormalLift_orthogonal
    (G : E →L[ℝ] E) (hpos : ∀ u : E, u ≠ 0 → 0 < inner ℝ (G u) u)
    (D : E →L[ℝ] N) (n : N) (w : E) (hw : D w = 0) :
    inner ℝ (G (metricNormalLift G D n)) w = 0 := by
  change inner ℝ (G (ContinuousLinearMap.inverse G
    (D.adjoint (ContinuousLinearMap.inverse (metricNormalGram G D) n)))) w = 0
  rw [(metricOperator_isInvertible_of_positive G hpos).self_apply_inverse,
    D.adjoint_inner_left, hw, inner_zero_right]

theorem metricNormalLift_unique
    (G : E →L[ℝ] E) (hpos : ∀ u : E, u ≠ 0 → 0 < inner ℝ (G u) u)
    (D : E →L[ℝ] N) (hD : Function.Surjective D) (n : N) (z : E) (hz : D z = n)
    (horth : ∀ w : E, D w = 0 → inner ℝ (G z) w = 0) : z = metricNormalLift G D n := by
  apply sub_eq_zero.mp
  by_contra hne
  have hd : D (z - metricNormalLift G D n) = 0 := by
    rw [map_sub, hz, metricNormalLift_rightInverse G hpos D hD n, sub_self]
  have h := hpos (z - metricNormalLift G D n) hne
  rw [map_sub, inner_sub_left, horth _ hd,
    metricNormalLift_orthogonal G hpos D n _ hd, sub_self] at h
  exact (lt_irrefl 0) h

theorem metricNormalLift_naturality
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [FiniteDimensional ℝ F]
    (G : E →L[ℝ] E) (G' : F →L[ℝ] F)
    (hpos : ∀ u : E, u ≠ 0 → 0 < inner ℝ (G u) u)
    (hpos' : ∀ u : F, u ≠ 0 → 0 < inner ℝ (G' u) u)
    (D : E →L[ℝ] N) (D' : F →L[ℝ] N) (hD : Function.Surjective D)
    (L : E ≃L[ℝ] F) (V : N ≃L[ℝ] N)
    (hmetric : ∀ u w, inner ℝ (G' (L u)) (L w) = inner ℝ (G u) w)
    (hcompat : ∀ u, D' (L u) = V (D u)) (n : N) :
    metricNormalLift G' D' (V n) = L (metricNormalLift G D n) := by
  have hD' : Function.Surjective D' := by
    intro y
    obtain ⟨z, hz⟩ := hD (V.symm y)
    refine ⟨L z, ?_⟩
    rw [hcompat, hz, V.apply_symm_apply]
  symm
  apply metricNormalLift_unique G' hpos' D' hD' (V n)
  · rw [hcompat, metricNormalLift_rightInverse G hpos D hD n]
  · intro w hw
    have hker : D (L.symm w) = 0 := by
      apply V.injective
      rw [map_zero, ← hcompat, L.apply_symm_apply, hw]
    calc
      inner ℝ (G' (L (metricNormalLift G D n))) w =
          inner ℝ (G' (L (metricNormalLift G D n))) (L (L.symm w)) := by
        rw [L.apply_symm_apply]
      _ = inner ℝ (G (metricNormalLift G D n)) (L.symm w) := hmetric _ _
      _ = 0 := metricNormalLift_orthogonal G hpos D n _ hker

#print axioms metricNormalLift_naturality

#print axioms metricNormalLift_unique

#print axioms metricNormalLift_orthogonal

#print axioms metricNormalLift_rightInverse

#print axioms metricNormalGram_bijective

#print axioms metricOperator_inverse_positive

end HodgeLean.Foundations.TubularEuler
