import HodgeLean.Foundations.Program.SchoenTowerL1bComponentTransform

/-! Exact ideals on reduced affine divisor charts.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A radical pullback divisor retains its exact ideal if no component lies in the pulled-back
centre. This allows charts with several divisor components. -/
theorem s2v_l1b_strictTransform_ideal_reduced_chart {X Y : Scheme} (f : X ⟶ Y)
    (D K : Y.IdealSheafData) (U : X.affineOpens)
    (hD : ((D.comap f).ideal U).IsRadical)
    (hK : ∀ q ∈ ((D.comap f).ideal U).minimalPrimes,
      ¬ (K.comap f).ideal U ≤ q) :
    (s2c_strictTransform f D K).ideal U = (D.comap f).ideal U := by
  rw [s2c_strictTransform, Scheme.IdealSheafData.vanishingIdeal_ideal]
  change PrimeSpectrum.vanishingIdeal
    (U.2.fromSpec ⁻¹' closure (f ⁻¹' ((D.support : Set Y) \ K.support))) = _
  rw [U.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    U.2.fromSpec.continuous]
  have hpre (I : Y.IdealSheafData) :
      U.2.fromSpec ⁻¹' (f ⁻¹' (I.support : Set Y)) =
        PrimeSpectrum.zeroLocus ((I.comap f).ideal U : Set Γ(X, U)) := by
    simpa only [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage] using
      s2v_l1b_affine_support_preimage (I.comap f) U
  rw [Set.preimage_sdiff, Set.preimage_sdiff, hpre D, hpre K,
    s2v_l1b_divisor_dense_of_minimalPrimes _ _ hK,
    PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
  exact hD.radical

end HodgeLean.Foundations.Program
