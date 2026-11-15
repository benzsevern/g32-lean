import Mathlib.Algebra.Field.Subfield.Basic
import HodgeLean.Foundations.Program.SchoenTowerI2aFieldCoefficientFactorization
import HodgeLean.Foundations.Program.SchoenCycleStep1Local
import HodgeLean.Foundations.Program.SchoenGenericPointMorphisms
import Mathlib.AlgebraicGeometry.Stalk

/-! # The actual generic field map of a dominant field point
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A dominant field point factors through the actual generic local ring, with a unique field embedding.
Source: Mathlib, Scheme.stalkClosedPointTo and the generic-point monomorphism. -/
theorem s2v_i2a_dominant_field_point_generic_factor
    (X : Scheme.{0}) [IsIntegral X] {K : Type} [Field K]
    (η : Spec (CommRingCat.of K) ⟶ X) [IsDominant η] :
    ∃! κ : X.functionField →+* K,
      Spec.map (CommRingCat.ofHom κ) ≫ X.fromSpecStalk (genericPoint X) = η := by
  have hg : η (IsLocalRing.closedPoint K) = genericPoint X := by
    have H := s2_dominant_genericPoint η
    have he : IsLocalRing.closedPoint K = genericPoint (Spec (CommRingCat.of K)) :=
      Subsingleton.elim _ _
    rwa [← he] at H
  let κ : X.functionField ⟶ CommRingCat.of K :=
    eqToHom (congrArg X.presheaf.stalk hg.symm) ≫ Scheme.stalkClosedPointTo η
  have hκ : Spec.map κ ≫ X.fromSpecStalk (genericPoint X) = η := by
    dsimp only [κ]
    rw [Spec.map_comp, Category.assoc]
    have H : Spec.map (eqToHom (congrArg X.presheaf.stalk hg.symm)) ≫
        X.fromSpecStalk (genericPoint X) = X.fromSpecStalk (η (IsLocalRing.closedPoint K)) := by
      have transport (x y : X) (h : x = y) :
          Spec.map (eqToHom (congrArg X.presheaf.stalk h.symm)) ≫ X.fromSpecStalk y =
            X.fromSpecStalk x := by
        subst y
        simp
      exact transport _ _ hg
    rw [H]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk η
  refine ⟨κ.hom, hκ, ?_⟩
  intro κ' hκ'
  have H : CommRingCat.ofHom κ' = κ := by
    apply Quiver.Hom.op_inj
    apply Scheme.Spec.map_injective
    change Spec.map (CommRingCat.ofHom κ') = Spec.map κ
    apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
    exact hκ'.trans hκ.symm
  exact congrArg CommRingCat.Hom.hom H

/-- The actual generic stalk map retains its scheme square for every dominant morphism of integral schemes.
Source: Mathlib, Scheme.SpecMap_stalkMap_fromSpecStalk and transport of the generic stalk. -/
theorem s2v_i2a_generic_stalk_map_square
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hg : f (genericPoint X) = genericPoint Y) :
    Spec.map (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫
      f.stalkMap (genericPoint X)) ≫ Y.fromSpecStalk (genericPoint Y) =
        X.fromSpecStalk (genericPoint X) ≫ f := by
  rw [Spec.map_comp, Category.assoc]
  have transport (x y : Y) (h : x = y) :
      Spec.map (eqToHom (congrArg Y.presheaf.stalk h.symm)) ≫ Y.fromSpecStalk y =
        Y.fromSpecStalk x := by
    subst y
    simp
  rw [transport _ _ hg, Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- Actual generic field embeddings commute with a retained generic stalk isomorphism.
Source: Mathlib, faithfulness of Spec and cancellation of the generic-point monomorphism. -/
theorem s2v_i2a_generic_field_embeddings_comp
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {K : Type} [Field K]
    (f : X ⟶ Y) (ηX : Spec (CommRingCat.of K) ⟶ X)
    (ηY : Spec (CommRingCat.of K) ⟶ Y) (hη : ηX ≫ f = ηY)
    (κX : X.functionField →+* K) (κY : Y.functionField →+* K)
    (hX : Spec.map (CommRingCat.ofHom κX) ≫ X.fromSpecStalk (genericPoint X) = ηX)
    (hY : Spec.map (CommRingCat.ofHom κY) ≫ Y.fromSpecStalk (genericPoint Y) = ηY)
    (E : Y.functionField ≅ X.functionField)
    (hE : Spec.map E.hom ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f) :
    κX.comp E.hom.hom = κY := by
  have H : CommRingCat.ofHom (κX.comp E.hom.hom) = CommRingCat.ofHom κY := by
    apply Quiver.Hom.op_inj
    apply Scheme.Spec.map_injective
    change Spec.map (CommRingCat.ofHom (κX.comp E.hom.hom)) =
      Spec.map (CommRingCat.ofHom κY)
    apply (cancel_mono (Y.fromSpecStalk (genericPoint Y))).mp
    have hh : CommRingCat.ofHom (κX.comp E.hom.hom) = E.hom ≫ CommRingCat.ofHom κX := rfl
    rw [hh, Spec.map_comp, Category.assoc, hE, ← Category.assoc, hX, hη, hY]
  exact congrArg CommRingCat.Hom.hom H

/-- The retained generic field embedding sends actual affine-open germs to the original coefficient map.
Source: Mathlib, Scheme.stalkClosedPointTo and the checked generic pullback equation for sections. -/
theorem s2v_i2a_generic_field_coefficients
    (X : Scheme.{0}) [IsIntegral X] {K : Type} [Field K]
    (η : Spec (CommRingCat.of K) ⟶ X) (κ : X.functionField →+* K)
    (hκ : Spec.map (CommRingCat.ofHom κ) ≫ X.fromSpecStalk (genericPoint X) = η)
    (U : X.Opens) [Nonempty U] (hη : ⊤ ≤ η ⁻¹ᵁ U) :
    κ.comp (X.germToFunctionField U).hom =
      (η.appLE U ⊤ hη ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom := by
  have hmem : X.fromSpecStalk (genericPoint X) (IsLocalRing.closedPoint X.functionField) ∈ U := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hgen : ⊤ ≤ (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem _ hmem).ge
  have H := s2v_i2a_field_point_open_coefficients_factor κ η
    (X.fromSpecStalk (genericPoint X)) hκ U hgen hη
  change κ.comp ((X.fromSpecStalk (genericPoint X)).appLE U ⊤ hgen ≫
    (Scheme.ΓSpecIso X.functionField).hom).hom = _ at H
  rw [s2e_step1_generic_appLE X U hgen] at H
  exact H

/-- The actual generic field image is exactly the subfield generated by the affine-open coefficients.
Source: Mathlib, functionField_isFractionRing_of_isAffineOpen and IsFractionRing.div_surjective. -/
theorem s2v_i2a_generic_field_range_eq_coefficient_closure
    (X : Scheme.{0}) [IsIntegral X] {K : Type} [Field K]
    (η : Spec (CommRingCat.of K) ⟶ X) (κ : X.functionField →+* K)
    (hκ : Spec.map (CommRingCat.ofHom κ) ≫ X.fromSpecStalk (genericPoint X) = η)
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (hη : ⊤ ≤ η ⁻¹ᵁ U) :
    let φ : Γ(X, U) →+* K := (η.appLE U ⊤ hη ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom
    κ.fieldRange = Subfield.closure (Set.range φ) := by
  intro φ
  letI : IsFractionRing Γ(X, U) X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  exact IsFractionRing.ringHom_fieldRange_eq_of_comp_eq
    (s2v_i2a_generic_field_coefficients X η κ hκ U hη)

/-- An actual open immersion of integral schemes induces its generic field isomorphism with the actual scheme square.
Source: Mathlib, the stalk isomorphisms of an open immersion and genericPoint_eq_of_isOpenImmersion. -/
theorem s2v_i2a_open_immersion_generic_field_iso
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (u : X ⟶ Y) [IsOpenImmersion u] :
    ∃ E : Y.functionField ≅ X.functionField,
      Spec.map E.hom ≫ Y.fromSpecStalk (genericPoint Y) =
        X.fromSpecStalk (genericPoint X) ≫ u := by
  have hg : u (genericPoint X) = genericPoint Y := genericPoint_eq_of_isOpenImmersion u
  let E : Y.functionField ≅ X.functionField :=
    eqToIso (congrArg Y.presheaf.stalk hg.symm) ≪≫ asIso (u.stalkMap (genericPoint X))
  refine ⟨E, ?_⟩
  change Spec.map (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫
    u.stalkMap (genericPoint X)) ≫ Y.fromSpecStalk (genericPoint Y) = _
  exact s2v_i2a_generic_stalk_map_square u hg

end HodgeLean.Foundations.Program
