import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.DualNumber

/-! # Explicit dual-number lifts of residue-valued derivations -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The first-order algebra map associated to a derivation and its specified residue map.
Source: Hartshorne, Algebraic Geometry, II.8, derivations and tangent vectors;
Mathlib, `derivationToSquareZeroEquivLift`. -/
def s2e_u1_derivationDualLift
    {R A K : Type*} [CommRing R] [CommRing A] [CommRing K]
    [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
    (d : Derivation R A K) : A →ₐ[R] DualNumber K where
  toFun a := TrivSqZeroExt.inl (algebraMap A K a) + TrivSqZeroExt.inr (d a)
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' a b := by ext <;> simp [map_add, add_assoc, add_left_comm, add_comm]
  map_mul' a b := by
    ext <;> simp [d.leibniz, Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl', mul_comm, add_comm]
  commutes' r := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl', ← IsScalarTower.algebraMap_apply R A K]

end HodgeLean.Foundations.Program
