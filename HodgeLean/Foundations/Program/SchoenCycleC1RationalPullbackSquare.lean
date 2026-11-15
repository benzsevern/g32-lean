import HodgeLean.Foundations.Program.SchoenCycleC1LocalSquareComposition

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An actual commutative scheme square yields the same rational embedding
on both paths when every original local stalk map is retained. -/
theorem s2e_c1_rational_pullback_square
    {X Y Z T : Scheme} [IsIntegral X] [IsIntegral Y] [IsIntegral Z] [IsIntegral T]
    (f : X ⟶ Y) (g : Y ⟶ T) (h : X ⟶ Z) (k : Z ⟶ T)
    (hsq : f ≫ g = h ≫ k)
    (α : Y.functionField →+* X.functionField) (β : T.functionField →+* Y.functionField)
    (γ : Z.functionField →+* X.functionField) (δ : T.functionField →+* Z.functionField)
    (hα : ∀ p (r : Y.presheaf.stalk (f p)),
      α (algebraMap (Y.presheaf.stalk (f p)) Y.functionField r) =
        algebraMap (X.presheaf.stalk p) X.functionField ((f.stalkMap p).hom r))
    (hβ : ∀ p (r : T.presheaf.stalk (g p)),
      β (algebraMap (T.presheaf.stalk (g p)) T.functionField r) =
        algebraMap (Y.presheaf.stalk p) Y.functionField ((g.stalkMap p).hom r))
    (hγ : ∀ p (r : Z.presheaf.stalk (h p)),
      γ (algebraMap (Z.presheaf.stalk (h p)) Z.functionField r) =
        algebraMap (X.presheaf.stalk p) X.functionField ((h.stalkMap p).hom r))
    (hδ : ∀ p (r : T.presheaf.stalk (k p)),
      δ (algebraMap (T.presheaf.stalk (k p)) T.functionField r) =
        algebraMap (Z.presheaf.stalk p) Z.functionField ((k.stalkMap p).hom r)) :
    α.comp β = γ.comp δ := by
  have he := s2e_c1_rational_local_square_comp h k γ δ hγ hδ
  rw [← hsq] at he
  exact (s2e_c1_generic_pullback_composition f g α β (γ.comp δ) hα hβ he).symm

end HodgeLean.Foundations.Program
