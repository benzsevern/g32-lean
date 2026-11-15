import HodgeLean.Foundations.Program.SchoenTowerCharacterStalk
import HodgeLean.Foundations.Program.SchoenTowerDeckOrder
import HodgeLean.Foundations.Program.SchoenTowerPullbackTopology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program
theorem s2v_projective_preimage_characterStalk {W B E : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom]
    (β : W ⟶ B) (j : E ⟶ B) (d : W ⟶ W) (hd : d ≫ β = β)
    (m : ℕ) (hm : 0 < m) (horder : (End.of d) ^ m = 1)
    (y : ComplexPoint E) (a : ℕ) (ha : ¬ m ∣ a)
    (hfix : ∀ x : ComplexPoint (s2b_preimage β j),
      Point.map (s2b_toExceptional β j) x = y →
        (Point.map (s2b_preimageDeck β j d hd))^[a] x = x)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) :
    let f := s2c_points.map (s2b_toExceptional β j)
    let δ := s2c_points.map (s2b_preimageDeck β j d hd)
    ∀ hδ : δ ≫ f = f,
      Subsingleton ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat)
        (X := s2c_points.obj E) (s2c_characterSheaf f δ hδ m ζ).obj y) := by
  dsimp only
  intro hδ
  exact s2v_characterStalk_primitive_inertia_subsingleton
    (s2c_points.map (s2b_toExceptional β j)) (s2v_projective_preimage_projection_proper β j)
    (s2c_points.map (s2b_preimageDeck β j d hd)) hδ m hm
    (s2v_preimageDeck_points_order β j d hd m horder) y a ha hfix ζ hζ

end HodgeLean.Foundations.Program
