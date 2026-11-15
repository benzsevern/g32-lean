import HodgeLean.Foundations.TubularEuler.NormalMetricLiftRegularityHelpers

/-! # Connection coefficients from real metric operators

The metric derivative and its real adjoint give the Koszul numerator in Hilbert coordinates.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.TubularEuler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def metricAdjointCLM : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
  (show (E →L[ℝ] E) →+ (E →L[ℝ] E) from
    { toFun := fun A => A.adjoint
      map_zero' := map_zero ContinuousLinearMap.adjoint
      map_add' := map_add ContinuousLinearMap.adjoint }).toRealLinearMap
    ContinuousLinearMap.adjoint.continuous

def metricKoszulNumerator (A : E →L[ℝ] E →L[ℝ] E) : E →L[ℝ] E →L[ℝ] E :=
  A + A.flip - metricAdjointCLM.comp A.flip

def metricConnectionCoefficient (G : E →L[ℝ] E) (A : E →L[ℝ] E →L[ℝ] E) :
    E →L[ℝ] E →L[ℝ] E :=
  (1 / 2 : ℝ) • ((ContinuousLinearMap.compL ℝ E E E) (ContinuousLinearMap.inverse G)).comp
    (metricKoszulNumerator A)

theorem metricConnectionCoefficient_apply (G : E →L[ℝ] E)
    (A : E →L[ℝ] E →L[ℝ] E) (u v : E) :
    metricConnectionCoefficient G A u v = (1 / 2 : ℝ) •
      ContinuousLinearMap.inverse G (A u v + A v u - (A.flip u).adjoint v) := by
  rfl

theorem metricConnectionCoefficient_koszul
    (G : E →L[ℝ] E) (hG : G.IsInvertible)
    (A : E →L[ℝ] E →L[ℝ] E) (u v w : E) :
    inner ℝ (G (metricConnectionCoefficient G A u v)) w = (1 / 2 : ℝ) *
      (inner ℝ (A u v) w + inner ℝ (A v u) w - inner ℝ (A w u) v) := by
  rw [metricConnectionCoefficient_apply, map_smul,
    hG.self_apply_inverse, inner_smul_left, inner_sub_left,
    inner_add_left, ContinuousLinearMap.adjoint_inner_left]
  rw [real_inner_comm (A.flip u w) v]
  simp only [starRingEnd_apply, star_trivial]
  rfl

theorem metricConnectionCoefficient_metric_compatible
    (G : E →L[ℝ] E) (hG : G.IsInvertible)
    (hGsym : ∀ v w, inner ℝ (G v) w = inner ℝ v (G w))
    (A : E →L[ℝ] E →L[ℝ] E)
    (hA : ∀ u v w, inner ℝ (A u v) w = inner ℝ v (A u w)) (u v w : E) :
    inner ℝ (G (metricConnectionCoefficient G A u v)) w +
      inner ℝ (G v) (metricConnectionCoefficient G A u w) = inner ℝ (A u v) w := by
  have hswap : inner ℝ (G v) (metricConnectionCoefficient G A u w) =
      inner ℝ (G (metricConnectionCoefficient G A u w)) v := by
    rw [hGsym, real_inner_comm (G (metricConnectionCoefficient G A u w)) v]
  have hsym : inner ℝ (A u w) v = inner ℝ (A u v) w := by
    rw [hA u w v, real_inner_comm (A u v) w]
  rw [hswap, metricConnectionCoefficient_koszul G hG,
    metricConnectionCoefficient_koszul G hG, hsym]
  ring

theorem metricConnectionCoefficient_symmetric
    (G : E →L[ℝ] E) (hG : G.IsInvertible)
    (A : E →L[ℝ] E →L[ℝ] E)
    (hA : ∀ u v w, inner ℝ (A u v) w = inner ℝ v (A u w)) (u v : E) :
    metricConnectionCoefficient G A u v = metricConnectionCoefficient G A v u := by
  obtain ⟨e, he⟩ := hG
  rw [← he]
  apply e.injective
  apply ext_inner_right ℝ
  intro w
  have h₁ := metricConnectionCoefficient_koszul (e : E →L[ℝ] E)
    ContinuousLinearMap.isInvertible_equiv A u v w
  have h₂ := metricConnectionCoefficient_koszul (e : E →L[ℝ] E)
    ContinuousLinearMap.isInvertible_equiv A v u w
  have hsym : inner ℝ (A w u) v = inner ℝ (A w v) u := by
    rw [hA w u v, real_inner_comm (A w v) u]
  calc
    _ = (1 / 2 : ℝ) *
        (inner ℝ (A u v) w + inner ℝ (A v u) w - inner ℝ (A w u) v) := h₁
    _ = (1 / 2 : ℝ) *
        (inner ℝ (A v u) w + inner ℝ (A u v) w - inner ℝ (A w v) u) := by
      rw [hsym]
      ring
    _ = _ := h₂.symm

theorem metricOperator_isInvertible_of_positive
    [FiniteDimensional ℝ E] (G : E →L[ℝ] E)
    (hpos : ∀ u : E, u ≠ 0 → 0 < inner ℝ (G u) u) : G.IsInvertible := by
  have hz : ∀ u : E, G u = 0 → u = 0 := by
    intro u hu
    by_contra hne
    have h := hpos u hne
    rw [hu, inner_zero_left] at h
    exact (lt_irrefl 0) h
  have hi : Function.Injective G := by
    intro u v huv
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub, huv, sub_self]
  have hs : Function.Surjective G := LinearMap.injective_iff_surjective.mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective G
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs), rfl⟩

#print axioms metricOperator_isInvertible_of_positive

#print axioms metricConnectionCoefficient_symmetric

#print axioms metricConnectionCoefficient_metric_compatible

#print axioms metricConnectionCoefficient_koszul

#print axioms metricConnectionCoefficient_apply

end HodgeLean.Foundations.TubularEuler
