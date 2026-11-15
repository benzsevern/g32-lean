import HodgeLean.Foundations.Program.SchoenCycleC1GenericLocalFieldSquare

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Rational pullbacks retaining the actual local stalk squares compose
contravariantly along the original scheme morphisms. -/
theorem s2e_c1_generic_pullback_composition
    {X Y Z : Scheme} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (α : Y.functionField →+* X.functionField)
    (β : Z.functionField →+* Y.functionField)
    (γ : Z.functionField →+* X.functionField)
    (hα : ∀ (p : X) (r : Y.presheaf.stalk (f p)),
      α (algebraMap (Y.presheaf.stalk (f p)) Y.functionField r) =
        algebraMap (X.presheaf.stalk p) X.functionField ((f.stalkMap p).hom r))
    (hβ : ∀ (p : Y) (r : Z.presheaf.stalk (g p)),
      β (algebraMap (Z.presheaf.stalk (g p)) Z.functionField r) =
        algebraMap (Y.presheaf.stalk p) Y.functionField ((g.stalkMap p).hom r))
    (hγ : ∀ (p : X) (r : Z.presheaf.stalk ((f ≫ g) p)),
      γ (algebraMap (Z.presheaf.stalk ((f ≫ g) p)) Z.functionField r) =
        algebraMap (X.presheaf.stalk p) X.functionField (((f ≫ g).stalkMap p).hom r)) :
    γ = α.comp β := by
  apply IsFractionRing.ringHom_ext (A := Z.presheaf.stalk ((f ≫ g) (genericPoint X)))
  intro r
  let p := genericPoint X
  change γ (algebraMap (Z.presheaf.stalk (g (f p))) Z.functionField r) =
    α (β (algebraMap (Z.presheaf.stalk (g (f p))) Z.functionField r))
  rw [hβ, hα]
  have he := hγ p r
  rw [Scheme.Hom.stalkMap_comp] at he
  exact he

end HodgeLean.Foundations.Program
