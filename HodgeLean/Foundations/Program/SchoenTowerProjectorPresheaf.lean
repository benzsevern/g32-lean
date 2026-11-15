import HodgeLean.Foundations.Program.SchoenTowerProjectorSections

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped BigOperators
namespace HodgeLean.Foundations.Program

def s2v_characterPresheafProjector {X E : TopCat} (f : X ⟶ E) (d : X ⟶ X)
    (hd : d ≫ f = f) (m : ℕ) (ζ : ℂ) : s2c_coverPresheaf f ⟶ s2c_coverPresheaf f :=
  ∑ t ∈ Finset.range m, s2c_coverPresheafScalar f ((m : ℂ)⁻¹ * ζ ^ (-(t : ℤ))) ≫
    ((End.of (s2c_coverPresheafDeck f d hd)) ^ t).asHom

theorem s2v_characterPresheafProjector_section {X E : TopCat}
    (f : X ⟶ E) (d : X ⟶ X) (hd : d ≫ f = f) (m : ℕ) (ζ : ℂ) (U : Opens E)
    (s : LocallyConstant {x : X // f x ∈ U} ℂ) :
    (s2v_characterPresheafProjector f d hd m ζ).app (op U) s =
      (∑ t ∈ Finset.range m, ((m : ℂ)⁻¹ * ζ ^ (-(t : ℤ))) •
        (LocallyConstant.comapₗ ℂ (s2v_coverOpenDeck f d hd U) :
          Module.End ℂ (LocallyConstant {x : X // f x ∈ U} ℂ)) ^ t) s := by
  classical
  have hsum {A B : AddCommGrpCat} (q : ℕ → (A ⟶ B)) (r : Finset ℕ) (a : A) :
      (∑ t ∈ r, q t) a = ∑ t ∈ r, q t a := by
    induction r using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; rfl
    | @insert i r hi ih =>
      rw [Finset.sum_insert hi, AddCommGrpCat.hom_add_apply, ih, Finset.sum_insert hi]
  have hscalar (c : ℂ) (r : LocallyConstant {x : X // f x ∈ U} ℂ) :
      (s2c_coverPresheafScalar f c).app (op U) r = c • r := rfl
  unfold s2v_characterPresheafProjector
  rw [NatTrans.app_sum, hsum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro t _
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply, hscalar,
    s2v_coverPresheafDeck_pow_section, map_smul]

theorem s2v_characterPresheafProjector_section_eigen {X E : TopCat}
    (f : X ⟶ E) (d : X ⟶ X) (hd : d ≫ f = f) (m : ℕ)
    (horder : ∀ x : X, d^[m] x = x) (ζ : ℂ) (hζ : ζ ^ m = 1) (hζ0 : ζ ≠ 0)
    (U : Opens E) (s : LocallyConstant {x : X // f x ∈ U} ℂ) :
    (s2c_coverPresheafDeck f d hd).app (op U)
      ((s2v_characterPresheafProjector f d hd m ζ).app (op U) s) =
      ζ • (show LocallyConstant {x : X // f x ∈ U} ℂ from
        (s2v_characterPresheafProjector f d hd m ζ).app (op U) s) := by
  let T : Module.End ℂ (LocallyConstant {x : X // f x ∈ U} ℂ) :=
    LocallyConstant.comapₗ ℂ (s2v_coverOpenDeck f d hd U)
  have hT : T ^ m = 1 := by
    ext r x
    change ((LocallyConstant.comapₗ ℂ (s2v_coverOpenDeck f d hd U)) ^ m) r x = r x
    rw [s2v_locallyConstant_comap_pow]
    congr 1
    apply Subtype.ext
    rw [s2v_coverOpenDeck_iterate, horder]
  rw [s2v_characterPresheafProjector_section]
  change T _ = ζ • _
  exact congrArg (fun q : Module.End ℂ (LocallyConstant {x : X // f x ∈ U} ℂ) => q s)
    (s2v_character_average_eigen T m hT ζ hζ hζ0)

theorem s2v_characterPresheafProjector_eigen {X E : TopCat}
    (f : X ⟶ E) (d : X ⟶ X) (hd : d ≫ f = f) (m : ℕ)
    (horder : ∀ x : X, d^[m] x = x) (ζ : ℂ) (hζ : ζ ^ m = 1) (hζ0 : ζ ≠ 0) :
    s2v_characterPresheafProjector f d hd m ζ ≫ s2c_coverPresheafDeck f d hd =
      s2v_characterPresheafProjector f d hd m ζ ≫ s2c_coverPresheafScalar f ζ := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  change LocallyConstant {x : X // f x ∈ U.unop} ℂ at s
  exact s2v_characterPresheafProjector_section_eigen f d hd m horder ζ hζ hζ0 U.unop s

end HodgeLean.Foundations.Program
