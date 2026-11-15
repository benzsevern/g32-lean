import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RingHom.Flat

/-! # The parameter map of the two-component residual node -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
namespace HodgeLean.Foundations.Program.G32Native.FibreC

/-- The node parameter is the product of its two independent affine coordinates. -/
def residualNodeMap (K : Type*) [CommRing K] :
    Polynomial K →+* Polynomial (Polynomial K) :=
  Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C)
    (Polynomial.C Polynomial.X * Polynomial.X)

/-- Setting the first node coordinate to one recovers the original parameter. -/
theorem residualNodeMap_retraction (K : Type*) [CommRing K] :
    (Polynomial.mapRingHom (Polynomial.evalRingHom (1 : K))).comp
      (residualNodeMap K) = RingHom.id (Polynomial K) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [residualNodeMap]
  · simp [residualNodeMap]

/-- The nodal parameter remains nonzero in the two-coordinate domain. -/
theorem residualNodeMap_injective (K : Type*) [CommRing K] :
    Function.Injective (residualNodeMap K) := by
  apply Function.LeftInverse.injective
    (g := Polynomial.mapRingHom (Polynomial.evalRingHom (1 : K)))
  intro p
  exact DFunLike.congr_fun (residualNodeMap_retraction K) p

/-- The product-coordinate family is flat over its affine parameter line. -/
theorem residualNodeMap_flat (K : Type*) [Field K] :
    (residualNodeMap K).Flat := by
  unfold RingHom.Flat
  letI : Algebra (Polynomial K) (Polynomial (Polynomial K)) := (residualNodeMap K).toAlgebra
  letI : Module (Polynomial K) (Polynomial (Polynomial K)) := Algebra.toModule
  change Module.Flat (Polynomial K) (Polynomial (Polynomial K))
  haveI : Module.IsTorsionFree (Polynomial K) (Polynomial (Polynomial K)) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (residualNodeMap_injective K)
  apply Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
  exact Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance

#print axioms residualNodeMap_flat
#print axioms residualNodeMap_injective
#print axioms residualNodeMap_retraction
end HodgeLean.Foundations.Program.G32Native.FibreC
