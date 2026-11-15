import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChartTensor

/-! # Polynomial presentations retaining the supplied pair-chart coefficient map -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial AlgebraicGeometry.RegularPairChart
namespace HodgeLean.Foundations.Program.G32Native

/-- A supplied pair-chart isomorphism gives its exact polynomial
presentation, with its original ratio and coefficient map.
Source: Hartshorne, Algebraic Geometry, II.7.13. -/
theorem paired_c3_pair_chart_presentation
    {A B : Type*} [CommRing A] [CommRing B] (u v : A)
    (e : ring u v ≃+* B) (f : A →+* B) (he : e.toRingHom.comp (coeff u v) = f) :
    f u = e (ratio u v) * f v ∧
      Function.Surjective (eval₂RingHom f (e (ratio u v))) ∧
      RingHom.ker (eval₂RingHom f (e (ratio u v))) = Ideal.span {C u - X * C v} := by
  have hc (a : A) : e (coeff u v a) = f a := DFunLike.congr_fun he a
  have hpres : eval₂RingHom f (e (ratio u v)) =
      e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {C u - X * C v})) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C]
      change f a = e (AlgebraicGeometry.RegularPairChart.coeff u v a)
      exact (hc a).symm
    · simp only [coe_eval₂RingHom, eval₂_X, RingHom.comp_apply, ratio]
      rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← hc u, ← hc v, ← map_mul]
    exact congrArg e (chart_relation u v)
  · rw [hpres]
    exact e.surjective.comp Ideal.Quotient.mk_surjective
  · rw [hpres, RingHom.ker_comp_of_injective _ e.injective, Ideal.mk_ker]

end HodgeLean.Foundations.Program.G32Native
