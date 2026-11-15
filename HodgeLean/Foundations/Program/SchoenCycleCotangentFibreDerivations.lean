import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.TensorProduct.Lift
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Detection of relative cotangent fibres by algebraic tangent derivations -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- If all relative tangent derivations to a field vanish, the actual relative cotangent fibre vanishes.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_cotangent_fibre_subsingleton_of_derivations
    (R A K : Type) [CommRing R] [CommRing A] [Field K]
    [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K]
    (h : Subsingleton (Derivation R A K)) : Subsingleton (K ⊗[A] Ω[A⁄R]) := by
  have hL : Subsingleton (Ω[A⁄R] →ₗ[A] K) :=
    (KaehlerDifferential.linearMapEquivDerivation (R := R) (S := A) (M := K)).toEquiv.subsingleton_congr.mpr h
  have hdual : Subsingleton ((K ⊗[A] Ω[A⁄R]) →ₗ[K] K) :=
    (LinearMap.liftBaseChangeEquiv K (R := A) (M := Ω[A⁄R]) (N := K)).toEquiv.subsingleton_congr.mp hL
  exact (Module.subsingleton_dual_iff K).mp hdual

end HodgeLean.Foundations.Program
