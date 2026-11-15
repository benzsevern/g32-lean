import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralCoefficientAction
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.RegularPairRatioOrbits
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.AffineChartPointFibre

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

section
variable {R K L : Type} [CommRing R] [Algebra ℂ R] [Field K] [Field L]
variable (u v : R)
local notation "A" => RegularPairChart.ring u v

/-- Every literal ratio fibre of the constructed original coefficient evaluation fibre is one orbit of the original field symmetry. -/
theorem integral_coefficient_ratio_fibre_orbit
    [IsDomain A] [IsIntegrallyClosed A]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra ℂ L] [IsScalarTower ℂ A L]
    [FiniteDimensional K L] [IsGalois K L]
    (φ : R →ₐ[ℂ] ℂ) (δ : L ≃ₐ[K] L) (hδ : orderOf δ = Module.finrank K L) :
    ∀ x y : integralCoefficientFibre (L := L) (regularPairCoefficientAlgHom u v) φ,
      x.val (algebraMap A (integralClosure A L) (RegularPairChart.ratio u v)) =
      y.val (algebraMap A (integralClosure A L) (RegularPairChart.ratio u v)) →
      ∃ n : ℕ, (integralCoefficientFibreDeck (regularPairCoefficientAlgHom u v) φ
        (δ.restrictScalars A))^[n] x = y := by
  let X := integralCoefficientFibre (L := L) (regularPairCoefficientAlgHom u v) φ
  let δA := δ.restrictScalars A
  let ρ := δA.mapIntegralClosure.toRingEquiv
  have hev : Function.Injective (fun x : X => x.val.toRingHom) := by
    intro x y h
    apply Subtype.ext
    exact AlgHom.toRingHom_injective h
  have hscalar (x : X) (c : ℂ) :
      x.val.toRingHom (algebraMap A (integralClosure A L) (algebraMap ℂ A c)) = c := by
    rw [← IsScalarTower.algebraMap_apply ℂ A (integralClosure A L) c]
    exact x.val.commutes c
  have hcoeff (x y : X) :
      (x.val.toRingHom.comp (algebraMap A (integralClosure A L))).comp
        (RegularPairChart.coeff u v) =
      (y.val.toRingHom.comp (algebraMap A (integralClosure A L))).comp
        (RegularPairChart.coeff u v) := by
    apply RingHom.ext
    intro r
    exact (x.property r).trans (y.property r).symm
  exact normalized_regular_pair_ratio_fibre_orbit u v δ hδ ρ (fun _ => rfl)
    (fun x : X => x.val.toRingHom) hev
    (integralCoefficientFibreDeck (regularPairCoefficientAlgHom u v) φ δA)
    (fun _ _ => rfl) hscalar hcoeff

end
end AlgebraicGeometry.RamifiedNormalization.StageFour
