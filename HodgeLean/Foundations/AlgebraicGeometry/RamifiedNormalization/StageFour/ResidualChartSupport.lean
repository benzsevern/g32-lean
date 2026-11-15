import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ResidualSupport
import HodgeLean.Foundations.Program.SchoenTowerL1bStrictTransformChart

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The actual residual transform has precisely the zero support of its chart ratio. -/
theorem residual_chart_support {X Y : Scheme} (f : X ⟶ Y)
    (D K : Y.IdealSheafData) (U : X.affineOpens) (s e : Γ(X, U))
    (hD : (D.comap f).ideal U = Ideal.span {s * e})
    (hK : (K.comap f).ideal U = Ideal.span {e})
    (he : IsRegular (Ideal.Quotient.mk (Ideal.span {s}) e)) :
    U.2.fromSpec ⁻¹' ((s2c_strictTransform f D K).support : Set X) =
      PrimeSpectrum.zeroLocus {s} := by
  change U.2.fromSpec ⁻¹' closure (f ⁻¹' ((D.support : Set Y) \ (K.support : Set Y))) = _
  rw [U.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    U.2.fromSpec.continuous]
  have hpre (I : Y.IdealSheafData) :
      U.2.fromSpec ⁻¹' (f ⁻¹' (I.support : Set Y)) =
        PrimeSpectrum.zeroLocus ((I.comap f).ideal U : Set Γ(X, U)) := by
    rw [← s2v_l1b_fromSpec_support (I.comap f) U,
      Scheme.IdealSheafData.support_comap]
    rfl
  rw [Set.preimage_diff, Set.preimage_diff, hpre D, hpre K, hD, hK,
    PrimeSpectrum.zeroLocus_span, PrimeSpectrum.zeroLocus_span]
  exact residual_regular_support s e he

end AlgebraicGeometry.RamifiedNormalization.StageFour
