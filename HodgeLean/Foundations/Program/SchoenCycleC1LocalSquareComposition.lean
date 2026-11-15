import HodgeLean.Foundations.Program.SchoenCycleC1GenericPullbackComposition

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Composing actual rational pullbacks retains every original local stalk
square for the composite scheme morphism. -/
theorem s2e_c1_rational_local_square_comp
    {X Y Z : Scheme} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (α : Y.functionField →+* X.functionField) (β : Z.functionField →+* Y.functionField)
    (hα : ∀ p (r : Y.presheaf.stalk (f p)),
      α (algebraMap (Y.presheaf.stalk (f p)) Y.functionField r) =
        algebraMap (X.presheaf.stalk p) X.functionField ((f.stalkMap p).hom r))
    (hβ : ∀ p (r : Z.presheaf.stalk (g p)),
      β (algebraMap (Z.presheaf.stalk (g p)) Z.functionField r) =
        algebraMap (Y.presheaf.stalk p) Y.functionField ((g.stalkMap p).hom r))
    (p : X) (r : Z.presheaf.stalk ((f ≫ g) p)) :
    (α.comp β) (algebraMap (Z.presheaf.stalk ((f ≫ g) p)) Z.functionField r) =
      algebraMap (X.presheaf.stalk p) X.functionField (((f ≫ g).stalkMap p).hom r) := by
  change α (β (algebraMap (Z.presheaf.stalk (g (f p))) Z.functionField r)) = _
  rw [hβ, hα, Scheme.Hom.stalkMap_comp]
  rfl

end HodgeLean.Foundations.Program
