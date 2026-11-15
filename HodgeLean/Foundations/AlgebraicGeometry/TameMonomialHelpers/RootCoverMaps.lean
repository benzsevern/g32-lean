import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.CoordinateRootCover
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Uniqueness of maps from the universal root cover
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace AlgebraicGeometry.TameMonomialCover.Helpers

/-- Maps from the coordinate-root tensor ring are determined by the original coefficients and the chosen coordinate roots.
Source: Mathlib, Algebra.TensorProduct.ringHom_ext and MvPolynomial.ringHom_ext. -/
theorem coordinate_root_tensor_ext
    {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] [Algebra k R]
    (n m : ℕ) (c : MvPolynomial (Fin n) k →ₐ[k] R) :
    let P := MvPolynomial (Fin n) k
    let B := ULift.{0} P
    letI := (rootParameterMap k n m).toRingHom.toAlgebra
    letI : SMul P B := (rootParameterMap k n m).toRingHom.toAlgebra.toSMul
    letI : Module P B := Algebra.toModule (R := P) (A := B)
    letI := c.toRingHom.toAlgebra
    let T := B ⊗[P] R
    ∀ f g : T →+* S,
      (∀ r, f (algebraMap R T r) = g (algebraMap R T r)) →
      (∀ j, f (algebraMap B T (ULift.up (MvPolynomial.X j))) =
        g (algebraMap B T (ULift.up (MvPolynomial.X j)))) → f = g := by
  intro P B
  letI := (rootParameterMap k n m).toRingHom.toAlgebra
  letI : SMul P B := (rootParameterMap k n m).toRingHom.toAlgebra.toSMul
  letI : Module P B := Algebra.toModule (R := P) (A := B)
  letI := c.toRingHom.toAlgebra
  intro T f g hR hX
  let up : P →+* B := ULift.ringEquiv.symm.toRingHom
  have hp : (f.comp (algebraMap B T)).comp up = (g.comp (algebraMap B T)).comp up := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change f (algebraMap B T (ULift.up (MvPolynomial.C r))) =
        g (algebraMap B T (ULift.up (MvPolynomial.C r)))
      have hC : ULift.up (MvPolynomial.C r) = algebraMap P B (MvPolynomial.C r) := by
        change ULift.up (MvPolynomial.C r) = ULift.up (MvPolynomial.expand m (MvPolynomial.C r))
        rw [MvPolynomial.expand_C]
      rw [hC, ← IsScalarTower.algebraMap_apply P B T,
        IsScalarTower.algebraMap_apply P R T]
      exact hR _
    · exact hX
  apply Algebra.TensorProduct.ringHom_ext
  · apply RingHom.ext
    intro b
    exact RingHom.congr_fun hp b.down
  · exact RingHom.ext hR

end AlgebraicGeometry.TameMonomialCover.Helpers
