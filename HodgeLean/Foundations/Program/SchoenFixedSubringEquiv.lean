import Mathlib.Algebra.Ring.Equiv
import Mathlib.RingTheory.Invariant.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- An equivariant ring equivalence restricts to an equivalence of the actual fixed subrings. -/
def s2_fixedSubringEquiv {A B G : Type} [CommRing A] [CommRing B] [Group G]
    [MulSemiringAction G A] [MulSemiringAction G B] (e : A ≃+* B)
    (he : ∀ (g : G) (a : A), e (g • a) = g • e a) :
    FixedPoints.subring A G ≃+* FixedPoints.subring B G where
  toFun a := ⟨e a.val, fun g => (he g a.val).symm.trans (congrArg e (a.property g))⟩
  invFun b := ⟨e.symm b.val, fun g => by
    apply e.injective
    rw [he, e.apply_symm_apply, b.property]⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a.val)
  right_inv b := Subtype.ext (e.apply_symm_apply b.val)
  map_mul' a b := Subtype.ext (e.map_mul a.val b.val)
  map_add' a b := Subtype.ext (e.map_add a.val b.val)

end HodgeLean.Foundations.Program
