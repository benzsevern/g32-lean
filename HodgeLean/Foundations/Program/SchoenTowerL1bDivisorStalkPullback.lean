import HodgeLean.Foundations.Program.SchoenTowerL1bKvalMaps
import HodgeLean.Foundations.Program.SchoenTowerL1bPullbackEquations

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A generic spectrum square identifies the two maps from every source stalk into the covering field. -/
theorem s2v_l1b_divisor_stalk_pullback
    {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (κX : X.functionField ⟶ CommRingCat.of K)
    (κY : Y.functionField ⟶ CommRingCat.of K)
    (hsq : Spec.map κX ≫ X.fromSpecStalk (genericPoint X) ≫ f =
      Spec.map κY ≫ Y.fromSpecStalk (genericPoint Y)) (x : X) :
    (s2v_l1b_kval_stalkMap X x κX).comp (f.stalkMap x).hom =
      s2v_l1b_kval_stalkMap Y (f x) κY := by
  change (f.stalkMap x ≫
    X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) ≫ κX).hom =
    (Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial) ≫ κY).hom
  apply congrArg CommRingCat.Hom.hom
  apply Spec.map_injective
  apply (cancel_mono (Y.fromSpecStalk (f x))).mp
  change Spec.map (f.stalkMap x ≫
      X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) ≫ κX) ≫ _ =
    Spec.map (Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial) ≫ κY) ≫ _
  simp only [Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkMap_fromSpecStalk,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc]
  exact hsq

/-- Equations for the same pulled-back ideal generate associated elements in the actual stalk. -/
theorem s2v_l1b_divisor_pullback_generators
    {X Y : Scheme.{0}} [IsIntegral X] (f : X ⟶ Y) (I : Y.IdealSheafData)
    (x : X) (U : X.affineOpens) (hxU : x ∈ U.1)
    (V : Y.affineOpens) (hxV : f x ∈ V.1)
    (g : Γ(Y, V)) (h : Γ(X, U))
    (hg : I.ideal V = Ideal.span {g})
    (hh : (I.comap f).ideal U = Ideal.span {h}) :
    Associated ((f.stalkMap x).hom ((Y.presheaf.germ V.1 (f x) hxV).hom g))
      ((X.presheaf.germ U.1 x hxU).hom h) := by
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ U.1 ⊓ f ⁻¹ᵁ V.1 from ⟨hxU, hxV⟩)
  have hWU' : W ≤ U.1 ⊓ f ⁻¹ᵁ V.1 := hWU
  let W' : X.affineOpens := ⟨W, hW⟩
  have hid : Ideal.span {(f.appLE V.1 W (hWU'.trans inf_le_right)).hom g} =
      Ideal.span {(X.presheaf.map (homOfLE (hWU'.trans inf_le_left)).op).hom h} := by
    rw [← Set.image_singleton, ← Ideal.map_span, ← hg,
      ← s2v_l1b_pullback_ideal_sections f I W' V (hWU'.trans inf_le_right),
      ← (I.comap f).map_ideal (show W' ≤ U from hWU'.trans inf_le_left),
      hh, Ideal.map_span, Set.image_singleton]
    rfl
  have H := congrArg (Ideal.map (X.presheaf.germ W x hxW).hom) hid
  simp only [Ideal.map_span, Set.image_singleton] at H
  have he : f.appLE V.1 W (hWU'.trans inf_le_right) ≫ X.presheaf.germ W x hxW =
      Y.presheaf.germ V.1 (f x) hxV ≫ f.stalkMap x := by
    rw [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res]
    exact (f.germ_stalkMap _ _ _).symm
  have he' := congrArg (fun k : Γ(Y, V) ⟶ X.presheaf.stalk x => k.hom g) he
  have hh' := congrArg (fun k : Γ(X, U) ⟶ X.presheaf.stalk x => k.hom h)
    (X.presheaf.germ_res (homOfLE (hWU'.trans inf_le_left)) x hxW)
  change (X.presheaf.germ W x hxW).hom ((f.appLE V.1 W (hWU'.trans inf_le_right)).hom g) = _ at he'
  change (X.presheaf.germ W x hxW).hom ((X.presheaf.map (homOfLE (hWU'.trans inf_le_left)).op).hom h) = _ at hh'
  rw [he', hh'] at H
  exact (Ideal.span_singleton_eq_span_singleton.mp H)

end HodgeLean.Foundations.Program
