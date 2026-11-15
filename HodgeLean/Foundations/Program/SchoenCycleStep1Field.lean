import HodgeLean.Foundations.Program.SchoenCycleStep1Glue

/-! # Pullback on the generic stalk under scheme isomorphisms -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

lemma s2e_step1_stalkCongr_fromSpec (X : Scheme) (x y : X) (h : x = y) :
    Spec.map (X.presheaf.stalkCongr (.of_eq h)).inv ≫ X.fromSpecStalk y =
      X.fromSpecStalk x := by
  subst y
  simp [TopCat.Presheaf.stalkCongr]

/-- Pullback on rational functions under an isomorphism.
Source: Hartshorne, Algebraic Geometry, II.3 (rational functions on integral schemes). -/
noncomputable def s2e_step1_fieldPullback (X : Scheme) [IsIntegral X]
    (u : X ⟶ X) [IsIso u] : X.functionField →+* X.functionField :=
  ((X.presheaf.stalkCongr (.of_eq (genericPoint_eq_of_isOpenImmersion u))).inv ≫
    u.stalkMap (genericPoint X)).hom

lemma s2e_step1_fieldPullback_generic (X : Scheme) [IsIntegral X]
    (u : X ⟶ X) [IsIso u] :
    Spec.map (CommRingCat.ofHom (s2e_step1_fieldPullback X u)) ≫
      X.fromSpecStalk (genericPoint X) = X.fromSpecStalk (genericPoint X) ≫ u := by
  change Spec.map ((X.presheaf.stalkCongr
    (.of_eq (genericPoint_eq_of_isOpenImmersion u))).inv ≫ u.stalkMap (genericPoint X)) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, s2e_step1_stalkCongr_fromSpec,
    Scheme.SpecMap_stalkMap_fromSpecStalk]
  exact genericPoint_eq_of_isOpenImmersion u

/-- Pullback of a rational germ is the germ of the pulled-back regular section. -/
lemma s2e_step1_fieldPullback_germ (X : Scheme) [IsIntegral X]
    (u : X ⟶ X) [IsIso u] (U V : X.Opens) [Nonempty U] [Nonempty V]
    (hUV : U ≤ u ⁻¹ᵁ V) :
    X.germToFunctionField V ≫ CommRingCat.ofHom (s2e_step1_fieldPullback X u) =
      u.appLE V U hUV ≫ X.germToFunctionField U := by
  change X.presheaf.germ V (genericPoint X) _ ≫
    (X.presheaf.stalkCongr (.of_eq (genericPoint_eq_of_isOpenImmersion u))).inv ≫
      u.stalkMap (genericPoint X) = _
  rw [TopCat.Presheaf.stalkCongr_inv, ← Category.assoc,
    X.presheaf.germ_stalkSpecializes, u.germ_stalkMap]
  rw [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res]

end HodgeLean.Foundations.Program
