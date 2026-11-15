import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.Algebra.Group.Commute.Units

/-! The function-field action induced by an invertible scheme map.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A positive finite order makes a scheme endomorphism invertible.
Source: the monoid of categorical endomorphisms. -/
theorem s2v_i2b_isIso_of_order
    {C : Type*} [Category C] {X : C} (d : X ⟶ X)
    (m : ℕ) (hm : 0 < m) (hd : (End.of d) ^ m = 1) : IsIso d := by
  have hunit : IsUnit (End.of d) := IsUnit.of_pow_eq_one hd (Nat.ne_of_gt hm)
  exact (CategoryTheory.isUnit_iff_isIso (End.of d)).mp hunit

/-- Conjugacy transports invertibility of the retained endomorphism.
Source: composition of categorical isomorphisms. -/
theorem s2v_i2b_isIso_of_conjugacy
    {C : Type*} [Category C] {X Y : C} (e : X ≅ Y)
    (d : X ⟶ X) [IsIso d] (d' : Y ⟶ Y)
    (hd : d ≫ e.hom = e.hom ≫ d') : IsIso d' := by
  have he : e.inv ≫ d ≫ e.hom = d' := by
    rw [hd, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  rw [← he]
  infer_instance

/-- Transport along equality of stalks preserves the canonical stalk-spectrum map.
Source: the canonical morphism from the spectrum of a stalk. -/
theorem s2v_i2b_fromSpecStalk_transport (X : Scheme) {x y : X} (h : x = y) :
    Spec.map (eqToHom (congrArg (fun z => X.presheaf.stalk z) h.symm)) ≫
      X.fromSpecStalk y = X.fromSpecStalk x := by
  subst y
  simp only [eqToHom_refl, Spec.map_id, Category.id_comp]

/-- An invertible scheme map induces a field automorphism with its actual generic-source square.
Source: naturality of the canonical stalk-spectrum morphism and invariance of the generic point. -/
theorem s2v_i2b_functionField_action
    (X : Scheme) [IsIntegral X] (d : X ⟶ X) [IsIso d] :
    ∃ δ : X.functionField ≃+* X.functionField,
      Spec.map (CommRingCat.ofHom δ.toRingHom) ≫
        X.fromSpecStalk (genericPoint X) =
      X.fromSpecStalk (genericPoint X) ≫ d := by
  have hg : d (genericPoint X) = genericPoint X := genericPoint_eq_of_isOpenImmersion d
  let e : X.functionField ≅ X.functionField :=
    eqToIso (congrArg (fun z => X.presheaf.stalk z) hg.symm) ≪≫
      asIso (d.stalkMap (genericPoint X))
  refine ⟨e.commRingCatIsoToRingEquiv, ?_⟩
  change Spec.map (eqToHom (congrArg (fun z => X.presheaf.stalk z) hg.symm) ≫
    d.stalkMap (genericPoint X)) ≫ X.fromSpecStalk (genericPoint X) = _
  rw [Spec.map_comp, Category.assoc,
    s2v_i2b_fromSpecStalk_transport X hg,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

end HodgeLean.Foundations.Program
