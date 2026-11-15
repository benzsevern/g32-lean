import HodgeLean.Foundations.Program.SchoenCycleAffinePointZeroLocus

/-! # Recovering reduced affine ideals from actual complex point sets -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A radical principal affine ideal is the actual ideal of the scheme closure of its complex zero set.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.2 and II.5. -/
theorem s2e_affine_point_closure_ideal
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (S : Set (ComplexPoint X)) (U : X.left.affineOpens) (c : Γ(X.left, U.1))
    (hrad : (Ideal.span ({c} : Set Γ(X.left, U.1))).IsRadical)
    (hzero : ∀ R : ComplexPoint X, R.underlying ∈ U.1 →
      (R ∈ S ↔ Point.evaluate U.1 c R = 0)) :
    (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (Point.underlying '' S))).ideal U = Ideal.span {c} := by
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  letI : JacobsonSpace (PrimeSpectrum Γ(X.left, U.1)) :=
    JacobsonSpace.of_isOpenEmbedding U.2.fromSpec.isOpenEmbedding
  let J := Ideal.span ({c} : Set Γ(X.left, U.1))
  have hs : U.2.fromSpec ⁻¹' (Point.underlying '' S) =
      PrimeSpectrum.zeroLocus J ∩ closedPoints (PrimeSpectrum Γ(X.left, U.1)) := by
    ext x
    constructor
    · rintro ⟨R, hRS, he⟩
      have hRU : R.underlying ∈ U.1 := by rw [he]; exact (U.2.isoSpec.inv x).2
      have hRc : IsClosed ({R.underlying} : Set X.left) :=
        (pointEquivClosedPoint X.hom ⟨R.left, Over.w R⟩).property
      refine ⟨(s2e_affine_zeroLocus_iff_evaluate_zero X U c x R he).mpr
        ((hzero R hRU).mp hRS), ?_⟩
      apply (Set.ext_iff.mp U.2.fromSpec.isOpenEmbedding.preimage_closedPoints x).mp
      change IsClosed ({U.2.fromSpec x} : Set X.left)
      rwa [← he]
    · rintro ⟨hxJ, hxc⟩
      have hcX : IsClosed ({U.2.fromSpec x} : Set X.left) :=
        U.2.fromSpec.closedPoints_subset_preimage_closedPoints hxc
      let R : ComplexPoint X := Over.homMk
        (pointOfClosedPoint X.hom (U.2.fromSpec x) hcX) (by simp)
      have he : R.underlying = U.2.fromSpec x :=
        pointOfClosedPoint_apply X.hom (U.2.fromSpec x) hcX _
      have hRU : R.underlying ∈ U.1 := by rw [he]; exact (U.2.isoSpec.inv x).2
      exact ⟨R, (hzero R hRU).mpr
        ((s2e_affine_zeroLocus_iff_evaluate_zero X U c x R he).mp hxJ), he⟩
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  change PrimeSpectrum.vanishingIdeal
    (U.2.fromSpec ⁻¹' closure (Point.underlying '' S)) = J
  rw [U.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    U.2.fromSpec.continuous, hs]
  have hZ : IsClosed (PrimeSpectrum.zeroLocus J : Set (PrimeSpectrum Γ(X.left, U.1))) :=
    PrimeSpectrum.isClosed_zeroLocus (R := Γ(X.left, U.1)) (J : Set Γ(X.left, U.1))
  have hcl := closure_inter_closedPoints hZ
  exact (congrArg PrimeSpectrum.vanishingIdeal hcl).trans
    ((PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical J).trans hrad.radical)

end HodgeLean.Foundations.Program
