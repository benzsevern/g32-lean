import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ResidualChartSupport
import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChart

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The retained coefficient square transports the original branch support to its literal chart equation. -/
theorem chart_support_coefficient_square {X B : Scheme}
    (f : X ⟶ B) (U : B.affineOpens) (u v w : Γ(B, U))
    (D : B.IdealSheafData) (hD : D.ideal U = Ideal.span {w})
    (j : Spec ↧(RegularPairChart.ring u v) ⟶ X)
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (RegularPairChart.coeff u v)) ≫ U.2.fromSpec) :
    j ⁻¹' (f ⁻¹' (D.support : Set B)) =
      PrimeSpectrum.zeroLocus {RegularPairChart.coeff u v w} := by
  change (j ≫ f) ⁻¹' (D.support : Set B) = _
  rw [hj]
  change (PrimeSpectrum.comap (RegularPairChart.coeff u v)) ⁻¹'
    (U.2.fromSpec ⁻¹' (D.support : Set B)) = _
  rw [s2v_l1b_fromSpec_support, hD, PrimeSpectrum.zeroLocus_span,
    PrimeSpectrum.preimage_comap_zeroLocus, Set.image_singleton]

end AlgebraicGeometry.RamifiedNormalization.StageFour
