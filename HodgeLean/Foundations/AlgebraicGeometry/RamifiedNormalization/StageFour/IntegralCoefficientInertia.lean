import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralCoefficientFixedPoints
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.SingleBranchEvaluationInertia

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The constructed coefficient-fibre deck action fixes each point with a vanishing etale branch coordinate after the original exponent iterate. -/
theorem integralCoefficientFibreDeck_branch_inertia
    {R A L : Type} [CommRing R] [CommRing A] [IsDomain A] [Field L]
    [Algebra ℂ R] [Algebra ℂ A] [Algebra A L] [Algebra ℂ L] [IsScalarTower ℂ A L]
    (f : R →ₐ[ℂ] A) (φ : R →ₐ[ℂ] ℂ)
    (n m α : ℕ) (hm : 0 < m)
    (c : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (hc : c.toRingHom.Etale)
    (hinj : Function.Injective (algebraMap A L)) (j : Fin n)
    (ε : A) (hε : IsUnit ε) (w : L)
    (hw : w ^ m = algebraMap A L ε * (algebraMap A L (c (MvPolynomial.X j))) ^ α)
    (hgen : Subfield.closure (Set.range (algebraMap A L) ∪ {w}) = ⊤)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (δ : L ≃ₐ[A] L) (hδ : δ w = algebraMap ℂ L ζ * w)
    (x : integralCoefficientFibre (L := L) f φ)
    (hzero : x.val (algebraMap A (integralClosure A L) (c (MvPolynomial.X j))) = 0) :
    (integralCoefficientFibreDeck f φ δ)^[α] x = x := by
  apply (integralCoefficientFibreDeck_fixed_iff f φ δ α x).mpr
  exact single_branch_integral_evaluation_inertia n m α hm A L c hc hinj j ε hε w hw
    hgen ζ hζ δ hδ x.val hzero

end AlgebraicGeometry.RamifiedNormalization.StageFour
