import HodgeLean.Foundations.Program.SchoenTowerProjectorPresheaf

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped BigOperators
namespace HodgeLean.Foundations.Program
theorem s2v_characterProjector_map_presheaf {X E : TopCat}
    (f : X ⟶ E) (d : X ⟶ X) (hd : d ≫ f = f) (m : ℕ) (ζ : ℂ) :
    (presheafToSheaf (Opens.grothendieckTopology E) AddCommGrpCat).map
      (s2v_characterPresheafProjector f d hd m ζ) = s2c_characterProjector f d hd m ζ := by
  let F := presheafToSheaf (Opens.grothendieckTopology E) AddCommGrpCat
  change F.map _ = _
  unfold s2v_characterPresheafProjector s2c_characterProjector
  rw [F.map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [F.map_comp]
  change F.map _ ≫ F.map _ = F.map _ ≫ _
  congr 1
  exact congrArg End.asHom
    ((F.mapEnd (s2c_coverPresheaf f)).map_pow (End.of (s2c_coverPresheafDeck f d hd)) t)

theorem s2v_characterProjector_eigen {X E : TopCat}
    (f : X ⟶ E) (d : X ⟶ X) (hd : d ≫ f = f) (m : ℕ)
    (horder : ∀ x : X, d^[m] x = x) (ζ : ℂ) (hζ : ζ ^ m = 1) (hζ0 : ζ ≠ 0) :
    s2c_characterProjector f d hd m ζ ≫ s2c_coverSheafDeck f d hd =
      s2c_characterProjector f d hd m ζ ≫ s2c_coverSheafScalar f ζ := by
  have h := congrArg
    (presheafToSheaf (Opens.grothendieckTopology E) AddCommGrpCat).map
    (s2v_characterPresheafProjector_eigen f d hd m horder ζ hζ hζ0)
  simp only [Functor.map_comp, s2v_characterProjector_map_presheaf] at h
  exact h

theorem s2v_characterImage_eigen {X E : TopCat}
    (f : X ⟶ E) (d : X ⟶ X) (hd : d ≫ f = f) (m : ℕ)
    (horder : ∀ x : X, d^[m] x = x) (ζ : ℂ) (hζ : ζ ^ m = 1) (hζ0 : ζ ≠ 0) :
    image.ι (s2c_characterProjector f d hd m ζ) ≫ s2c_coverSheafDeck f d hd =
      image.ι (s2c_characterProjector f d hd m ζ) ≫ s2c_coverSheafScalar f ζ := by
  apply (cancel_epi (factorThruImage (s2c_characterProjector f d hd m ζ))).mp
  simpa only [← Category.assoc, image.fac] using
    s2v_characterProjector_eigen f d hd m horder ζ hζ hζ0

end HodgeLean.Foundations.Program
