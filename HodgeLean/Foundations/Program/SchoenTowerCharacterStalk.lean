import HodgeLean.Foundations.Program.SchoenTowerStalkInertia
import HodgeLean.Foundations.Program.SchoenTowerProjectorSheaf

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace HodgeLean.Foundations.Program
theorem s2v_characterStalk_fixed_iterate_subsingleton {X E : TopCat}
    (f : X ⟶ E) (hf : IsProperMap f) (d : X ⟶ X) (hd : d ≫ f = f)
    (m : ℕ) (horder : ∀ x : X, d^[m] x = x)
    (y : E) (a : ℕ) (hfix : ∀ x : X, f x = y → d^[a] x = x)
    (ζ : ℂ) (hζ : ζ ^ m = 1) (hζ0 : ζ ≠ 0) (hζa : ζ ^ a ≠ 1) :
    Subsingleton ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat) (X := E)
      (s2c_characterSheaf f d hd m ζ).obj y) := by
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat y
  let S := TopCat.Sheaf.forget AddCommGrpCat E ⋙ T
  let P := s2c_characterProjector f d hd m ζ
  let i := S.map (image.ι P)
  haveI : Mono i := by
    dsimp only [i]
    infer_instance
  have hi := (AddCommGrpCat.mono_iff_injective i).mp inferInstance
  have hz (v : ↥(S.obj (image P))) : i v = 0 := by
    have hvec : T.map (s2c_coverSheafDeck f d hd).hom (i v) =
        T.map (s2c_coverSheafScalar f ζ).hom (i v) := by
      have he := congrArg S.map (s2v_characterImage_eigen f d hd m horder ζ hζ hζ0)
      simp only [Functor.map_comp] at he
      exact congrArg (fun h => h v) he
    exact s2v_coverSheafStalk_fixed_iterate_vanishing f hf d hd y a hfix ζ hζa (i v) hvec
  exact ⟨fun v w => hi ((hz v).trans (hz w).symm)⟩

theorem s2v_characterStalk_primitive_inertia_subsingleton {X E : TopCat}
    (f : X ⟶ E) (hf : IsProperMap f) (d : X ⟶ X) (hd : d ≫ f = f)
    (m : ℕ) (hm : 0 < m) (horder : ∀ x : X, d^[m] x = x)
    (y : E) (a : ℕ) (ha : ¬ m ∣ a)
    (hfix : ∀ x : X, f x = y → d^[a] x = x)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) :
    Subsingleton ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat) (X := E)
      (s2c_characterSheaf f d hd m ζ).obj y) :=
  s2v_characterStalk_fixed_iterate_subsingleton f hf d hd m horder y a hfix ζ
    hζ.pow_eq_one (hζ.ne_zero (Nat.ne_of_gt hm))
    (fun h => ha ((hζ.pow_eq_one_iff_dvd a).mp h))

end HodgeLean.Foundations.Program
