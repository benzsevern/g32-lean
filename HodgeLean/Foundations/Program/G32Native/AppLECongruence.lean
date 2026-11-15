import Mathlib.AlgebraicGeometry.Scheme

/-! Congruence for restriction maps attached to equal scheme morphisms. -/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Equal scheme morphisms induce equal section maps on specified source and target opens. -/
theorem g32l4_appLE_congr_morphism {X Y : Scheme.{0}} {f g : Y ⟶ X}
    (h : f = g) (U : X.Opens) (V : Y.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

end HodgeLean.Foundations.Program
