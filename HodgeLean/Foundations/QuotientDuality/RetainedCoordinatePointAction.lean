import HodgeLean.Foundations.QuotientDuality.RetainedCoordinateGroup
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Basic

/-! The actual continuous action of the finite coordinate subgroup on complex points. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.Adapters
open HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

variable (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (n : ℕ)

instance retainedCoordinateGroupFinite :
    Finite (retainedCoordinateSubgroup S Y a e ha1 hamul n) :=
  (retainedCoordinateSubgroup_finite S Y a e ha1 hamul n).to_subtype

instance retainedCoordinateGroupFintype :
    Fintype (retainedCoordinateSubgroup S Y a e ha1 hamul n) := Fintype.ofFinite _

instance retainedCoordinatePointAction :
    MulAction (retainedCoordinateSubgroup S Y a e ha1 hamul n)
      (ComplexPoint (g3_power Y n)) where
  smul g x := Point.map g.val.asIso.hom x
  one_smul x := by
    change x ≫ 𝟙 _ = x
    exact Category.comp_id x
  mul_smul g h x := by
    change x ≫ (h.val.asIso.hom ≫ g.val.asIso.hom) =
      (x ≫ h.val.asIso.hom) ≫ g.val.asIso.hom
    exact (Category.assoc _ _ _).symm

instance retainedCoordinatePointContinuous :
    ContinuousConstSMul (retainedCoordinateSubgroup S Y a e ha1 hamul n)
      (ComplexPoint (g3_power Y n)) where
  continuous_const_smul g := Point.continuous_map g.val.asIso.hom

def retainedCoordinateElement (v : Fin n → ZMod S.m) (hv : (∑ i, v i) = 0)
    (σ : Equiv.Perm (Fin n)) : retainedCoordinateSubgroup S Y a e ha1 hamul n :=
  ⟨Aut.of (retainedCoordinateIso S Y a e ha1 hamul n v σ), v, hv, σ, rfl⟩

#print axioms retainedCoordinatePointAction
#print axioms retainedCoordinatePointContinuous
end HodgeLean.Foundations.QuotientDuality
