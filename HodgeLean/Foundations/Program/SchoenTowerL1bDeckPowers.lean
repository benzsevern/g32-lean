import HodgeLean.Foundations.Program.SchoenTowerL1bKummerAction

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The original generic action square respects all natural powers. -/
theorem s2v_l1b_deck_generic_powers
    (X : Scheme.{0}) [IsIntegral X]
    (d : X ⟶ X) (φ : X.functionField ≃+* X.functionField)
    (hφ : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      X.fromSpecStalk (genericPoint X) = X.fromSpecStalk (genericPoint X) ≫ d)
    (k : ℕ) :
    Spec.map (CommRingCat.ofHom (φ ^ k).toRingHom) ≫
      X.fromSpecStalk (genericPoint X) =
      X.fromSpecStalk (genericPoint X) ≫ (End.of d ^ k).asHom := by
  induction k with
  | zero =>
    change Spec.map (𝟙 X.functionField) ≫ _ = _ ≫ 𝟙 X
    rw [Spec.map_id, Category.id_comp, Category.comp_id]
  | succ k ih =>
    rw [pow_succ φ k, pow_succ' (End.of d) k, End.mul_asHom]
    change Spec.map (CommRingCat.ofHom ((φ ^ k).toRingHom.comp φ.toRingHom)) ≫ _ =
      _ ≫ ((End.of d ^ k).asHom ≫ d)
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hφ,
      ← Category.assoc, ih, Category.assoc]

/-- A symmetry over a separated base and its actual generic-field action have equal order. -/
theorem s2v_l1b_deck_generic_order
    (X T : Scheme.{0}) [IsIntegral X] (s : X ⟶ T) [IsSeparated s]
    (d : X ⟶ X) (hd : d ≫ s = s)
    (φ : X.functionField ≃+* X.functionField)
    (hφ : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      X.fromSpecStalk (genericPoint X) = X.fromSpecStalk (genericPoint X) ≫ d) :
    orderOf φ = orderOf (End.of d) := by
  haveI := s2_genericPointMorphism_dominant X
  have hb (k : ℕ) : (End.of d ^ k).asHom ≫ s = s := by
    induction k with
    | zero => exact Category.id_comp _
    | succ k ih =>
      rw [pow_succ, End.mul_asHom, Category.assoc, ih, hd]
  apply orderOf_eq_orderOf_iff.mpr
  intro k
  have hp := s2v_l1b_deck_generic_powers X d φ hφ k
  constructor
  · intro hk
    apply End.ext
    apply ext_of_isDominant_of_isSeparated s
      ((hb k).trans (Category.id_comp s).symm) (X.fromSpecStalk (genericPoint X))
    rw [← hp, hk]
    change Spec.map (𝟙 X.functionField) ≫ _ = _ ≫ 𝟙 X
    rw [Spec.map_id, Category.id_comp, Category.comp_id]
  · intro hk
    have he : CommRingCat.ofHom (φ ^ k).toRingHom = 𝟙 X.functionField := by
      apply Spec.map_injective
      apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
      rw [hp, hk]
      change X.fromSpecStalk (genericPoint X) ≫ 𝟙 X =
        Spec.map (𝟙 X.functionField) ≫ X.fromSpecStalk (genericPoint X)
      rw [Spec.map_id, Category.id_comp, Category.comp_id]
    ext z
    exact congrArg (fun f : X.functionField ⟶ X.functionField => f z) he

end HodgeLean.Foundations.Program
