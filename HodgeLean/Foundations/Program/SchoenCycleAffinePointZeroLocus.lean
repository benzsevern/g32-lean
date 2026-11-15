import HodgeLean.Foundations.Program.SchoenCycleProjectiveLinearPointSet

/-! # Affine prime zero loci and actual complex section evaluation -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- A prime represented by an actual complex point contains the principal section ideal exactly when that section evaluates to zero.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.2 and II.5. -/
theorem s2e_affine_zeroLocus_iff_evaluate_zero
    (X : Over (Spec ↧ℂ)) (U : X.left.affineOpens) (c : Γ(X.left, U.1))
    (x : PrimeSpectrum Γ(X.left, U.1)) (R : ComplexPoint X)
    (he : R.underlying = U.2.fromSpec x) :
    x ∈ PrimeSpectrum.zeroLocus (Ideal.span ({c} : Set Γ(X.left, U.1))) ↔
      Point.evaluate U.1 c R = 0 := by
  have hRU : R.underlying ∈ U.1 := by
    rw [he]
    exact (U.2.isoSpec.inv x).2
  have hb : x ∈ PrimeSpectrum.basicOpen c ↔ R.underlying ∈ X.left.basicOpen c := by
    rw [← U.2.fromSpec_preimage_basicOpen c]
    change U.2.fromSpec x ∈ X.left.basicOpen c ↔ _
    rw [← he]
  have hh := hb.trans (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero c R hRU)
  simpa [PrimeSpectrum.zeroLocus_span] using not_congr hh

end HodgeLean.Foundations.Program
