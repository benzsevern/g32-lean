import HodgeLean.Foundations.Program.SchoenTowerProjectorSheaf

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped BigOperators
namespace HodgeLean.Foundations.Program

theorem s2v_character_average_fixes_eigenvector {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (m : ℕ) (hm : 0 < m) (ζ : ℂ) (hζ0 : ζ ≠ 0)
    (v : V) (hv : T v = ζ • v) :
    (∑ t ∈ Finset.range m, ((m : ℂ)⁻¹ * ζ ^ (-(t : ℤ))) • T ^ t) v = v := by
  have hp (t : ℕ) : (T ^ t) v = ζ ^ t • v := by
    induction t with
    | zero => simp only [pow_zero, Module.End.one_apply, one_smul]
    | succ t ih =>
      rw [pow_succ, Module.End.mul_apply, hv, map_smul, ih, smul_smul, pow_succ']
  have hc (t : ℕ) : ((m : ℂ)⁻¹ * ζ ^ (-(t : ℤ))) * ζ ^ t = (m : ℂ)⁻¹ := by
    rw [zpow_neg, zpow_natCast, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hζ0), mul_one]
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, hp, smul_smul, hc,
    Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hm0, one_smul]

theorem s2v_characterPresheafProjector_idempotent {X E : TopCat}
    (f : X ⟶ E) (d : X ⟶ X) (hd : d ≫ f = f) (m : ℕ) (hm : 0 < m)
    (horder : ∀ x : X, d^[m] x = x) (ζ : ℂ) (hζ : ζ ^ m = 1) (hζ0 : ζ ≠ 0) :
    s2v_characterPresheafProjector f d hd m ζ ≫
      s2v_characterPresheafProjector f d hd m ζ = s2v_characterPresheafProjector f d hd m ζ := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  change LocallyConstant {x : X // f x ∈ U.unop} ℂ at s
  let T : Module.End ℂ (LocallyConstant {x : X // f x ∈ U.unop} ℂ) :=
    LocallyConstant.comapₗ ℂ (s2v_coverOpenDeck f d hd U.unop)
  let v : LocallyConstant {x : X // f x ∈ U.unop} ℂ :=
    (s2v_characterPresheafProjector f d hd m ζ).app U s
  have he : T v = ζ • v :=
    s2v_characterPresheafProjector_section_eigen f d hd m horder ζ hζ hζ0 U.unop s
  change (s2v_characterPresheafProjector f d hd m ζ).app U v = v
  rw [s2v_characterPresheafProjector_section]
  exact s2v_character_average_fixes_eigenvector T m hm ζ hζ0 v he

theorem s2v_characterProjector_idempotent {X E : TopCat}
    (f : X ⟶ E) (d : X ⟶ X) (hd : d ≫ f = f) (m : ℕ) (hm : 0 < m)
    (horder : ∀ x : X, d^[m] x = x) (ζ : ℂ) (hζ : ζ ^ m = 1) (hζ0 : ζ ≠ 0) :
    s2c_characterProjector f d hd m ζ ≫ s2c_characterProjector f d hd m ζ =
      s2c_characterProjector f d hd m ζ := by
  have h := congrArg
    (presheafToSheaf (Opens.grothendieckTopology E) AddCommGrpCat).map
    (s2v_characterPresheafProjector_idempotent f d hd m hm horder ζ hζ hζ0)
  simp only [Functor.map_comp, s2v_characterProjector_map_presheaf] at h
  exact h

theorem s2v_characterImage_retraction {X E : TopCat}
    (f : X ⟶ E) (d : X ⟶ X) (hd : d ≫ f = f) (m : ℕ) (hm : 0 < m)
    (horder : ∀ x : X, d^[m] x = x) (ζ : ℂ) (hζ : ζ ^ m = 1) (hζ0 : ζ ≠ 0) :
    image.ι (s2c_characterProjector f d hd m ζ) ≫
      factorThruImage (s2c_characterProjector f d hd m ζ) = 𝟙 _ := by
  apply (cancel_mono (image.ι (s2c_characterProjector f d hd m ζ))).mp
  simp only [Category.assoc, image.fac, Category.id_comp]
  apply (cancel_epi (factorThruImage (s2c_characterProjector f d hd m ζ))).mp
  simpa only [← Category.assoc, image.fac] using
    s2v_characterProjector_idempotent f d hd m hm horder ζ hζ hζ0

end HodgeLean.Foundations.Program
