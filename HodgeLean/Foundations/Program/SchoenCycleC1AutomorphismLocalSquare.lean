import HodgeLean.Foundations.Program.SchoenCycleC1GenericLocalFieldSquare
import HodgeLean.Foundations.Program.SchoenCycleStep1Field

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The original automorphism rational pullback retains every moving-point
stalk square, without requiring that the selected point be fixed. -/
theorem s2e_c1_automorphism_rational_local_square
    (X : Scheme) [IsIntegral X] (f : X ⟶ X) [IsIso f]
    (p : X) (r : X.presheaf.stalk (f p)) :
    s2e_step1_fieldPullback X f (algebraMap (X.presheaf.stalk (f p)) X.functionField r) =
      algebraMap (X.presheaf.stalk p) X.functionField ((f.stalkMap p).hom r) := by
  have transport (x y : X) (h : x = y) :
      (X.presheaf.stalkCongr (.of_eq h)).inv = eqToHom (congrArg X.presheaf.stalk h.symm) := by
    subst y
    simp [TopCat.Presheaf.stalkCongr, TopCat.Presheaf.stalkSpecializes_refl]
  dsimp only [s2e_step1_fieldPullback]
  rw [transport _ _ (genericPoint_eq_of_isOpenImmersion f)]
  exact s2e_c1_generic_stalk_map_local_square f (genericPoint_eq_of_isOpenImmersion f) p r

end HodgeLean.Foundations.Program
