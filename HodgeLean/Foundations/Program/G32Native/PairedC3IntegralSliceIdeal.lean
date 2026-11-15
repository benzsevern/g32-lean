import HodgeLean.Foundations.Program.G32Native.PairedC3AffineSliceCoefficient

/-! # Prime slice ideals and branch cancellation on affine neighborhoods -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual affine ideal of a nonempty part of an integral closed
slice is prime.
Source: Hartshorne, Algebraic Geometry, II.3. -/
theorem paired_c3_integral_slice_prime
    {Q X : Scheme} [IsIntegral Q] (i : Q ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) [Nonempty (i ⁻¹ᵁ U.1)] :
    (i.ker.ideal U).IsPrime := by
  rw [Scheme.Hom.ker_apply]
  exact RingHom.ker_isPrime (i.app U.1).hom

#print axioms paired_c3_integral_slice_prime
/-- A branch with proper restriction cancels modulo the actual affine
slice ideal, using regularity on the integral slice section ring.
Source: Hartshorne, Algebraic Geometry, II.3 and II.6. -/
theorem paired_c3_integral_slice_cancel
    {Q X : Scheme} [IsIntegral Q] (i : Q ⟶ X) [IsClosedImmersion i]
    (D : X.IdealSheafData) (hproper : (D.comap i).support ≠ ⊤)
    (U : X.affineOpens) [Nonempty (i ⁻¹ᵁ U.1)]
    (u : Γ(X, U)) (hu : D.ideal U = Ideal.span {u}) :
    ∀ x : Γ(X, U), u * x ∈ i.ker.ideal U → x ∈ i.ker.ideal U := by
  have hreg := paired_c3_restricted_branch_regular i D hproper U u hu
  intro x hx
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at hx ⊢
  apply hreg
  change (i.app U.1).hom u * (i.app U.1).hom x = (i.app U.1).hom u * 0
  rw [mul_zero, ← map_mul]
  exact hx

#print axioms paired_c3_integral_slice_cancel
end HodgeLean.Foundations.Program.G32Native
