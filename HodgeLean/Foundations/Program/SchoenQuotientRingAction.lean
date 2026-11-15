import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- An ideal preserved by a ring action carries the actual induced action on its quotient ring. -/
def s2_quotientRingAction {A G : Type} [CommRing A] [Group G] [MulSemiringAction G A]
    (I : Ideal A) (hI : ∀ g : G, ∀ a ∈ I, g • a ∈ I) : MulSemiringAction G (A ⧸ I) where
  smul g := Ideal.quotientMap (I := I) I (MulSemiringAction.toRingHom G A g) (hI g)
  one_smul x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk I ((1 : G) • a) = Ideal.Quotient.mk I a
    rw [one_smul]
  mul_smul g h x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk I ((g * h) • a) = Ideal.Quotient.mk I (g • (h • a))
    rw [mul_smul]
  smul_zero g := (Ideal.quotientMap (I := I) I (MulSemiringAction.toRingHom G A g) (hI g)).map_zero
  smul_add g x y := (Ideal.quotientMap (I := I) I (MulSemiringAction.toRingHom G A g) (hI g)).map_add x y
  smul_one g := (Ideal.quotientMap (I := I) I (MulSemiringAction.toRingHom G A g) (hI g)).map_one
  smul_mul g x y := (Ideal.quotientMap (I := I) I (MulSemiringAction.toRingHom G A g) (hI g)).map_mul x y

end HodgeLean.Foundations.Program
