import HodgeLean.Foundations.Program.SchoenTowerL1bAffineTransform

/-! Reduced-transform ideals on affine charts meeting the exceptional divisor.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A prime pullback divisor has its exact pullback ideal as reduced transform when the centre
misses its generic point, even if the chart meets the exceptional divisor. -/
theorem s2v_l1b_strictTransform_ideal_prime_chart {X Y : Scheme} (f : X ⟶ Y)
    (D K : Y.IdealSheafData) (U : X.affineOpens)
    [((D.comap f).ideal U).IsPrime]
    (hK : ¬ (K.comap f).ideal U ≤ (D.comap f).ideal U) :
    (s2c_strictTransform f D K).ideal U = (D.comap f).ideal U := by
  rw [s2c_strictTransform, Scheme.IdealSheafData.vanishingIdeal_ideal]
  change PrimeSpectrum.vanishingIdeal
    (U.2.fromSpec ⁻¹' closure (f ⁻¹' ((D.support : Set Y) \ K.support))) = _
  rw [U.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    U.2.fromSpec.continuous]
  have hD : U.2.fromSpec ⁻¹' (f ⁻¹' (D.support : Set Y)) =
      PrimeSpectrum.zeroLocus ((D.comap f).ideal U : Set Γ(X, U)) := by
    simpa only [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage] using
      s2v_l1b_affine_support_preimage (D.comap f) U
  have hC : U.2.fromSpec ⁻¹' (f ⁻¹' (K.support : Set Y)) =
      PrimeSpectrum.zeroLocus ((K.comap f).ideal U : Set Γ(X, U)) := by
    simpa only [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage] using
      s2v_l1b_affine_support_preimage (K.comap f) U
  rw [Set.preimage_sdiff, Set.preimage_sdiff, hD, hC,
    s2v_l1b_prime_divisor_dense _ _ hK,
    PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
  exact Ideal.IsPrime.radical inferInstance

end HodgeLean.Foundations.Program
