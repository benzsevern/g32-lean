import HodgeLean.Foundations.Program.SchoenTowerI2aRootCoverNormality
import Mathlib.RingTheory.RingHom.Etale

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The faithfully embedded etale complex chart is integrally closed, as detected at its maximal localizations. -/
theorem etale_complex_chart_integrally_closed
    {A : Type*} [CommRing A] [IsDomain A] [Algebra ℂ A]
    (N : ℕ) (c : MvPolynomial (Fin N) ℂ →ₐ[ℂ] A) (hc : c.toRingHom.Etale) :
    IsIntegrallyClosed A := by
  let P := MvPolynomial (Fin N) ℂ
  letI : Algebra P A := c.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ P A := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro z
    exact (c.commutes z).symm)
  letI : Algebra.Etale P A := hc.toAlgebra
  letI : Algebra.Smooth ℂ A := Algebra.Smooth.comp ℂ P A
  apply IsIntegrallyClosed.of_localization_maximal
  intro Q _ hQ
  letI : Q.IsPrime := hQ.isPrime
  exact (HodgeLean.Foundations.Program.s2v_i2a_complex_smooth_localization_normal A Q).2

end AlgebraicGeometry.RamifiedNormalization.StageFour
