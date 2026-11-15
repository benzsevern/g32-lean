import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralCoefficientAction
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.CoordinateEigenvalues

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The canonical integral selector and parameter inherit the original generator's two scalar eigenvalues on every coefficient-fibre evaluation. -/
theorem integral_binomial_eigenvalues
    {R A L : Type} [CommRing R] [CommRing A] [Field L]
    [Algebra ℂ R] [Algebra ℂ A] [Algebra A L] [Algebra ℂ L] [IsScalarTower ℂ A L]
    (f : R →ₐ[ℂ] A) (φ : R →ₐ[ℂ] ℂ) (δ : L ≃ₐ[A] L)
    (r : A) (w : L) (ζ : ℂ)
    (hw : δ w = algebraMap ℂ L ζ * w)
    (n a : ℕ) (i j : ℤ) (q t : integralClosure A L)
    (hq : (q : L) = w ^ n / (algebraMap A L r) ^ a)
    (ht : (t : L) = (algebraMap A L r) ^ i * w ^ j) :
    ∀ z : integralCoefficientFibre (L := L) f φ,
      (integralCoefficientFibreDeck f φ δ z).val q = ζ ^ n * z.val q ∧
      (integralCoefficientFibreDeck f φ δ z).val t = ζ ^ j * z.val t := by
  have he := binomial_coordinate_eigenvalues δ.toRingEquiv (algebraMap A L r) w
    (algebraMap ℂ L ζ) (δ.commutes r) hw n a i j
  have hq' : δ.mapIntegralClosure q = algebraMap ℂ (integralClosure A L) (ζ ^ n) * q := by
    apply Subtype.ext
    change δ (q : L) = algebraMap ℂ L (ζ ^ n) * (q : L)
    rw [hq]
    simpa only [map_pow, AlgEquiv.coe_toRingEquiv] using he.1
  have ht' : δ.mapIntegralClosure t = algebraMap ℂ (integralClosure A L) (ζ ^ j) * t := by
    apply Subtype.ext
    change δ (t : L) = algebraMap ℂ L (ζ ^ j) * (t : L)
    rw [ht]
    simpa only [map_zpow₀, AlgEquiv.coe_toRingEquiv] using he.2
  intro z
  constructor
  · change z.val (δ.mapIntegralClosure q) = _
    rw [hq', map_mul, AlgHom.commutes]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
  · change z.val (δ.mapIntegralClosure t) = _
    rw [ht', map_mul, AlgHom.commutes]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]

end AlgebraicGeometry.RamifiedNormalization.StageFour
