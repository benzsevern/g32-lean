import Mathlib.GroupTheory.Perm.Basic

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The actual regular permutation representation in a specified finite enumeration. -/
def s2_regularPermutation {G : Type} [Group G] {n : ℕ} (e : Fin n ≃ G) :
    G →* Equiv.Perm (Fin n) where
  toFun g := e.trans ((Equiv.mulLeft g).trans e.symm)
  map_one' := by
    ext i
    simp
  map_mul' g h := by
    ext i
    simp [mul_assoc]

end HodgeLean.Foundations.Program
