import Mathlib.Algebra.DualNumber

/-! # Base-field equivalences on dual numbers -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A scalar algebra equivalence transports both components of a dual number.
Source: Hartshorne, Algebraic Geometry, II.8, the dual-number tangent test. -/
def s2e_u1_dualNumberCongr
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) : DualNumber A ≃ₐ[R] DualNumber B where
  toFun x := TrivSqZeroExt.inl (e x.fst) + TrivSqZeroExt.inr (e x.snd)
  invFun y := TrivSqZeroExt.inl (e.symm y.fst) + TrivSqZeroExt.inr (e.symm y.snd)
  left_inv x := by ext <;> simp
  right_inv y := by ext <;> simp
  map_mul' x y := by
    ext
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
        TrivSqZeroExt.fst_mul, map_mul, add_zero]
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
        DualNumber.snd_mul, map_mul, map_add, zero_add, add_zero]
  map_add' x y := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

end HodgeLean.Foundations.Program
