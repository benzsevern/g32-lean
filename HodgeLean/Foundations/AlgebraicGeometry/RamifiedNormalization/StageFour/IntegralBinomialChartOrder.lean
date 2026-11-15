import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.PrimitiveChartOrder
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralCoefficientAction

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A nonzero ratio evaluation in an actual integral binomial chart retains the exact primitive scheme deck order. -/
theorem integral_binomial_chart_order
    {R A L : Type} [CommRing R] [CommRing A] [Field L]
    [Algebra ℂ R] [Algebra ℂ A] [Algebra A L] [Algebra ℂ L] [IsScalarTower ℂ A L]
    (f : R →ₐ[ℂ] A) (φ : R →ₐ[ℂ] ℂ) (δ : L ≃ₐ[A] L)
    (F : Over (Spec ↧ℂ)) (D : F ⟶ F) (m α : ℕ) (hm : 0 < m)
    (hperiod : (End.of D) ^ m = 1)
    (H : integralCoefficientFibre (L := L) f φ → ComplexPoint F) (hH : Function.Injective H)
    (hD : ∀ z, H (integralCoefficientFibreDeck f φ δ z) = Point.map D (H z))
    (ε r : A) (hε : IsUnit ε) (w : integralClosure A L)
    (heq : w ^ m = algebraMap A (integralClosure A L) (ε * r ^ α))
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (hw : δ (w : L) = algebraMap ℂ L ζ * (w : L))
    (z : integralCoefficientFibre (L := L) f φ)
    (hs : z.val (algebraMap A (integralClosure A L) r) ≠ 0) :
    orderOf (End.of D) = m := by
  have hz : z.val w ≠ 0 := by
    have hu : z.val (algebraMap A (integralClosure A L) ε) ≠ 0 :=
      ((hε.map (algebraMap A (integralClosure A L))).map z.val.toRingHom).ne_zero
    intro hz
    have hh := congrArg z.val heq
    simp only [map_pow, map_mul] at hh
    rw [hz, zero_pow (Nat.ne_of_gt hm)] at hh
    exact mul_ne_zero hu (pow_ne_zero α hs) hh.symm
  have hwEigen : δ.mapIntegralClosure w = algebraMap ℂ (integralClosure A L) ζ * w := by
    apply Subtype.ext
    exact hw
  apply endomorphism_order_of_primitive_chart_evaluation D m hm hperiod
    (integralCoefficientFibreDeck f φ δ) H hH hD ζ hζ (fun a => a.val w) (fun a => ?_) z hz
  change a.val (δ.mapIntegralClosure w) = _
  rw [hwEigen, map_mul, AlgHom.commutes]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]

end AlgebraicGeometry.RamifiedNormalization.StageFour
