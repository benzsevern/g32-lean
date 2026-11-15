import HodgeLean.Foundations.Program.SchoenTowerCharacterEigenspace
import HodgeLean.Foundations.Program.SchoenTowerDeckOrder

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

theorem s2v_preimage_character_eigenspace_of_comparison {W B E : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (d : W ⟶ W) (hd : d ≫ β = β)
    (m : ℕ) (hm : 0 < m) (horder : (End.of d) ^ m = 1)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (n : ℕ) :
    let f := s2c_points.map (s2b_toExceptional β j)
    let δ := s2c_points.map (s2b_preimageDeck β j d hd)
    ∀ (hδ : δ ≫ f = f)
      (c : AlgebraicTopology.Singular.Cohomology ℂ
        (s2c_points.obj (s2b_preimage β j)) n ≃+ Sheaf.H (s2c_coverSheaf f) n),
      (∀ v, c (s2b_preimageCohomologyDeck β j d hd n v) =
        Sheaf.H.map (s2c_coverSheafDeck f δ hδ) n (c v)) →
      (∀ (z : ℂ) v, c (z • v) =
        Sheaf.H.map (s2c_coverSheafScalar f z) n (c v)) →
      ∃ e : Sheaf.H (s2c_characterSheaf f δ hδ m ζ) n ≃+
        ↥(Module.End.eigenspace (s2b_preimageCohomologyDeck β j d hd n) ζ),
        ∀ v, c (e v).val = Sheaf.H.map
          (image.ι (s2c_characterProjector f δ hδ m ζ)) n v := by
  dsimp only
  intro hδ c hcD hcS
  exact s2v_character_H_eigenspace_of_comparison
    (s2c_points.map (s2b_toExceptional β j))
    (s2c_points.map (s2b_preimageDeck β j d hd)) hδ m hm
    (s2v_preimageDeck_points_order β j d hd m horder) ζ
    hζ.pow_eq_one (hζ.ne_zero (Nat.ne_of_gt hm))
    (s2b_preimageCohomologyDeck β j d hd n) n c hcD hcS

end HodgeLean.Foundations.Program
