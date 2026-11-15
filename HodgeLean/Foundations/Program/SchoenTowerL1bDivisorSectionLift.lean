import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorGenericStalk
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorSpecialization

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Compatibility on function fields determines the pullback of every section germ. -/
theorem s2v_l1b_divisor_section_stalk_lift
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (x : Y) (y : X)
    (φ : Y.presheaf.stalk x →+* X.presheaf.stalk y)
    (hφ : ∀ a, s2v_l1b_functionFieldPullback f (algebraMap _ Y.functionField a) =
      algebraMap _ X.functionField (φ a))
    (U : Y.Opens) (hx : x ∈ U) (hy : f y ∈ U) (g : Γ(Y, U)) :
    φ (Y.presheaf.germ U x hx g) =
      (f.stalkMap y).hom (Y.presheaf.germ U (f y) hy g) := by
  letI : Nonempty U := ⟨⟨x, hx⟩⟩
  apply IsFractionRing.injective (X.presheaf.stalk y) X.functionField
  rw [← hφ, ← s2v_l1b_divisor_generic_stalk,
    Y.algebraMap_germ_eq_germToFunctionField hx,
    Y.algebraMap_germ_eq_germToFunctionField hy]

/-- Compatibility on function fields identifies the lift with specialization followed by stalk pullback. -/
theorem s2v_l1b_divisor_specialization_stalk_lift
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (x : Y) (y : X)
    (φ : Y.presheaf.stalk x →+* X.presheaf.stalk y)
    (hφ : ∀ a, s2v_l1b_functionFieldPullback f (algebraMap _ Y.functionField a) =
      algebraMap _ X.functionField (φ a))
    (hgen : f y ⤳ x) (a : Y.presheaf.stalk x) :
    φ a = (f.stalkMap y).hom ((Y.presheaf.stalkSpecializes hgen).hom a) := by
  apply IsFractionRing.injective (X.presheaf.stalk y) X.functionField
  rw [← hφ, ← s2v_l1b_divisor_generic_stalk, s2v_l1b_divisor_specialization_function_field]

end HodgeLean.Foundations.Program
