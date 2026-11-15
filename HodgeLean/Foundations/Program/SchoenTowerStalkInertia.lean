import HodgeLean.Foundations.Program.SchoenTowerCoverStalk

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory TopologicalSpace
namespace HodgeLean.Foundations.Program

theorem s2v_coverStalk_fixed_iterate_vanishing {X E : TopCat}
    (f : X ⟶ E) (hf : IsProperMap f) (d : X ⟶ X) (hd : d ≫ f = f)
    (y : E) (a : ℕ) (hfix : ∀ x : X, f x = y → d^[a] x = x)
    (ζ : ℂ) (hζ : ζ ^ a ≠ 1) (v : (s2c_coverPresheaf f).stalk y)
    (hv : (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
        (s2c_coverPresheafDeck f d hd) v =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
        (s2c_coverPresheafScalar f ζ) v) : v = 0 := by
  let g : {x : X // f x = y} → {x : X // f x = y} := fun x =>
    ⟨d x.val, (congrArg (fun h : X ⟶ E => h x.val) hd).trans x.property⟩
  let w : {x : X // f x = y} → ℂ := s2v_coverStalkEvaluation f y v
  have hw (x : {x : X // f x = y}) : w (g x) = ζ * w x := by
    have h := congrArg (fun t => s2v_coverStalkEvaluation f y t x) hv
    rw [s2v_coverStalkEvaluation_deck, s2v_coverStalkEvaluation_scalar] at h
    exact h
  have hi (n : ℕ) : ∀ x, w (g^[n] x) = ζ ^ n * w x := by
    induction n with
    | zero => intro x; simp only [Function.iterate_zero_apply, pow_zero, one_mul]
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', hw, ih, pow_succ']
      exact (mul_assoc _ _ _).symm
  have hsem : Function.Semiconj (fun x : {x : X // f x = y} => x.val)
      g (fun x : X => d x) := fun _ => rfl
  have hg (x : {x : X // f x = y}) : g^[a] x = x :=
    Subtype.ext (((hsem.iterate_right a) x).trans (hfix x.val x.property))
  apply s2v_coverStalkEvaluation_injective f hf y
  have hz : s2v_coverStalkEvaluation f y 0 = 0 := map_zero _
  rw [hz]
  funext x
  have hx : ζ ^ a * w x = 1 * w x := by
    rw [one_mul, ← hi a x, hg]
  exact (mul_eq_mul_right_iff.mp hx).resolve_left hζ

theorem s2v_coverStalk_primitive_inertia_vanishing {X E : TopCat}
    (f : X ⟶ E) (hf : IsProperMap f) (d : X ⟶ X) (hd : d ≫ f = f)
    (y : E) (m a : ℕ) (ha : ¬ m ∣ a)
    (hfix : ∀ x : X, f x = y → d^[a] x = x)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (v : (s2c_coverPresheaf f).stalk y)
    (hv : (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
        (s2c_coverPresheafDeck f d hd) v =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
        (s2c_coverPresheafScalar f ζ) v) : v = 0 :=
  s2v_coverStalk_fixed_iterate_vanishing f hf d hd y a hfix ζ
    (fun h => ha ((hζ.pow_eq_one_iff_dvd a).mp h)) v hv

theorem s2v_coverSheafStalk_fixed_iterate_vanishing {X E : TopCat}
    (f : X ⟶ E) (hf : IsProperMap f) (d : X ⟶ X) (hd : d ≫ f = f)
    (y : E) (a : ℕ) (hfix : ∀ x : X, f x = y → d^[a] x = x)
    (ζ : ℂ) (hζ : ζ ^ a ≠ 1) (v : ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat) (X := E) (s2c_coverSheaf f).obj y))
    (hv : (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
        (s2c_coverSheafDeck f d hd).hom v =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
        (s2c_coverSheafScalar f ζ).hom v) : v = 0 := by
  let J := Opens.grothendieckTopology E
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat y
  let τ : s2c_coverPresheaf f ⟶ (s2c_coverSheaf f).obj := toSheafify J _
  letI : IsIso τ := s2v_coverPresheaf_toSheafify_isIso f
  let φ := T.map τ
  haveI : IsIso φ := inferInstance
  have hφ := (ConcreteCategory.isIso_iff_bijective φ).mp inferInstance
  obtain ⟨w, hw⟩ := hφ.2 v
  have hn (q : s2c_coverPresheaf f ⟶ s2c_coverPresheaf f) :
      T.map q ≫ φ = φ ≫ T.map (((presheafToSheaf J AddCommGrpCat).map q).hom) := by
    change T.map q ≫ T.map τ = T.map τ ≫ T.map (sheafifyMap J q)
    rw [← T.map_comp, ← T.map_comp]
    exact congrArg T.map (toSheafify_naturality J q)
  have he (q : s2c_coverPresheaf f ⟶ s2c_coverPresheaf f) :
      φ (T.map q w) = T.map (((presheafToSheaf J AddCommGrpCat).map q).hom) (φ w) := by
    exact congrArg (fun h => h w) (hn q)
  have hwv : T.map (s2c_coverPresheafDeck f d hd) w =
      T.map (s2c_coverPresheafScalar f ζ) w := by
    apply hφ.1
    rw [he, he, hw]
    exact hv
  have hw0 := s2v_coverStalk_fixed_iterate_vanishing f hf d hd y a hfix ζ hζ w hwv
  calc
    v = φ w := hw.symm
    _ = φ 0 := congrArg φ hw0
    _ = 0 := map_zero _

end HodgeLean.Foundations.Program
