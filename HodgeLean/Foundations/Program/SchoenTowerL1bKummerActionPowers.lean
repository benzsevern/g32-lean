import HodgeLean.Foundations.Program.SchoenTowerL1bKummerAction

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A compatible generic spectrum square remains compatible under every natural power. -/
theorem s2v_l1b_generic_square_pow
    {X : Scheme.{0}} [IsIntegral X]
    (φ : End X.functionField) (d : End X)
    (hφ : Spec.map φ.asHom ≫ X.fromSpecStalk (genericPoint X) =
      X.fromSpecStalk (genericPoint X) ≫ d.asHom) (n : ℕ) :
    Spec.map (φ ^ n).asHom ≫ X.fromSpecStalk (genericPoint X) =
      X.fromSpecStalk (genericPoint X) ≫ (d ^ n).asHom := by
  induction n with
  | zero => simp only [pow_zero, End.one_def, Spec.map_id, Category.id_comp,
      Category.comp_id]
  | succ n ih =>
    rw [pow_succ' φ, pow_succ d, End.mul_asHom, End.mul_asHom]
    change Spec.map ((φ ^ n).asHom ≫ φ.asHom) ≫ _ = _ ≫ (d.asHom ≫ (d ^ n).asHom)
    rw [Spec.map_comp, Category.assoc, ih, ← Category.assoc, hφ, Category.assoc]

/-- A separated scheme detects periods of a symmetry on its actual generic field. -/
theorem s2v_l1b_generic_period_iff
    {X T : Scheme.{0}} [IsIntegral X]
    (s : X ⟶ T) [IsSeparated s]
    (φ : End X.functionField) (d : End X) (hd : d.asHom ≫ s = s)
    (hφ : Spec.map φ.asHom ≫ X.fromSpecStalk (genericPoint X) =
      X.fromSpecStalk (genericPoint X) ≫ d.asHom) (n : ℕ) :
    φ ^ n = 1 ↔ d ^ n = 1 := by
  have hbase : ∀ n : ℕ, (d ^ n).asHom ≫ s = s := by
    intro n
    induction n with
    | zero => simp only [pow_zero, End.one_def, Category.id_comp]
    | succ n ih =>
      rw [pow_succ, End.mul_asHom]
      change (d.asHom ≫ (d ^ n).asHom) ≫ s = s
      rw [Category.assoc, ih, hd]
  have hsquare := s2v_l1b_generic_square_pow φ d hφ n
  constructor
  · intro h
    haveI := s2_genericPointMorphism_dominant X
    apply End.ext
    apply ext_of_isDominant_of_isSeparated s
      (by simpa only [End.one_def, Category.id_comp] using hbase n)
      (X.fromSpecStalk (genericPoint X))
    rw [← hsquare, h]
    simp only [End.one_def, Spec.map_id, Category.id_comp, Category.comp_id]
  · intro h
    apply End.ext
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
    rw [hsquare, h]
    simp only [End.one_def, Spec.map_id, Category.id_comp, Category.comp_id]

/-- A compatible generic action has exactly the order of its separated scheme symmetry. -/
theorem s2v_l1b_generic_order_eq
    {X T : Scheme.{0}} [IsIntegral X]
    (s : X ⟶ T) [IsSeparated s]
    (φ : End X.functionField) (d : End X) (hd : d.asHom ≫ s = s)
    (hφ : Spec.map φ.asHom ≫ X.fromSpecStalk (genericPoint X) =
      X.fromSpecStalk (genericPoint X) ≫ d.asHom) :
    orderOf φ = orderOf d := by
  exact orderOf_eq_orderOf_iff.mpr (s2v_l1b_generic_period_iff s φ d hd hφ)

end HodgeLean.Foundations.Program
