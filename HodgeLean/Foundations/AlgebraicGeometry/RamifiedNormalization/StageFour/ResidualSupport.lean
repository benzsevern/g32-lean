import HodgeLean.Foundations.Program.SchoenTowerL1bRegularTransform

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A parameter regular on the residual divisor preserves its full support after removing the centre. -/
theorem residual_regular_support {R : Type*} [CommRing R] (s e : R)
    (he : IsRegular (Ideal.Quotient.mk (Ideal.span {s}) e)) :
    closure (PrimeSpectrum.zeroLocus {s * e} \ PrimeSpectrum.zeroLocus {e}) =
      PrimeSpectrum.zeroLocus {s} := by
  have havoid : ∀ q ∈ (Ideal.span {s}).minimalPrimes, ¬ Ideal.span {e} ≤ q := by
    intro q hq hle
    exact s2v_l1b_regular_quotient_avoids_components s e he q hq
      (hle (Ideal.subset_span (Set.mem_singleton e)))
  rw [PrimeSpectrum.zeroLocus_singleton_mul, Set.union_sdiff_right,
    ← PrimeSpectrum.zeroLocus_span {s}, ← PrimeSpectrum.zeroLocus_span {e}]
  exact s2v_l1b_divisor_dense_of_minimalPrimes _ _ havoid

end AlgebraicGeometry.RamifiedNormalization.StageFour
