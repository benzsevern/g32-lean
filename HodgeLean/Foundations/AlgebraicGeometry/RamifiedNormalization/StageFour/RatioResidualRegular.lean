import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.RatioResidualQuotient

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Regularity of the other original parameter persists modulo the literal chart ratio. -/
theorem ratio_residual_denominator_regular {R : Type*} [CommRing R] (u v : R)
    (hv : IsRegular (Ideal.Quotient.mk (Ideal.span {u}) v)) :
    IsRegular (Ideal.Quotient.mk (Ideal.span {RegularPairChart.ratio u v})
      (RegularPairChart.coeff u v v)) := by
  let E := ratioResidualEquiv u v
  have hE (r : R) : E (Ideal.Quotient.mk (Ideal.span {RegularPairChart.ratio u v})
      (RegularPairChart.coeff u v r)) = Ideal.Quotient.mk (Ideal.span {u}) r := E.commutes r
  constructor
  · intro a b hab
    apply E.injective
    apply hv.left
    dsimp only at hab ⊢
    rw [← hE v, ← map_mul, ← map_mul, hab]
  · intro a b hab
    apply E.injective
    apply hv.right
    dsimp only at hab ⊢
    rw [← hE v, ← map_mul, ← map_mul, hab]

end AlgebraicGeometry.RamifiedNormalization.StageFour
