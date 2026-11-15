import HodgeLean.Papers.SkeletonG34FiniteProofs

/-! # G34 finite coverage statements (FROZEN SPEC) -/
set_option maxHeartbeats 200000

noncomputable section
open CategoryTheory
namespace HodgeLean.Papers

/-- The two explicit nonsplit norm classes from the type-III example.
The quaternionic varieties and polarization realization are not asserted here.
Source: G34 v1.5, Example 12.2. -/
theorem skelg34_typeIII_classes :
    skelg34_pureNorm (-3) (-1) 0 1 0 = 1 ∧
    skelg34_pureNorm (-3) (-1) 1 0 0 = 3 ∧
    skelg34_pureNorm (-3) (-1) 1 0 2 = 15 ∧
    skelg34_pureNorm (-3) (-1) 1 4 1 = 22 ∧
    skelg34_pureNorm (-3) (-1) 1 0 1 = 6 ∧
    (1 * 3 * 15 : ℚ) = 45 ∧ (22 * 3 * 6 : ℚ) = 396 ∧
    SameNormClass 3 (-45) (-5) ∧ SameNormClass 3 (-396) (-11) ∧
    ¬ SameNormClass 3 (-5) (-1) ∧ ¬ SameNormClass 3 (-11) (-1) :=
  skelg34_typeIII_classes_aux

/-- The determinant formula and division by the quadratic generator in the printed basis.
This is a matrix identity, without a quaternionic polarization-realization assertion.
Source: G34 v1.5, Example 12.2. -/
theorem skelg34_typeIII_determinant (a b α β γ : ℚ) (u : ℂ) (hu : u^2 = (a : ℂ)) :
    (skelg34_typeIIIGram b α β γ u).det = (-b * skelg34_pureNorm a b α β γ : ℚ) ∧
    (u⁻¹ • skelg34_typeIIIGram b α β γ u).det =
      ((-b * skelg34_pureNorm a b α β γ / a : ℚ) : ℂ) :=
  skelg34_typeIII_determinant_aux a b α β γ u hu

/-- Premise witness for `G34ClassDatumStatement`: an order-three character and six nontrivial
branch elements, with the identity change of generator and conjugacy representatives. -/
example : ∃ χ : (⊤ : Subgroup (Multiplicative (ZMod 3))) →* Multiplicative (ZMod 3),
    (3 ≤ (3 : ℕ)) ∧ Function.Surjective χ ∧
    (∀ h, Multiplicative.toAdd (χ h) =
      ((1 : (ZMod 3)ˣ) : ZMod 3) * Multiplicative.toAdd (χ h)) ∧
    ∀ i : Fin 6,
      IsConj (Multiplicative.ofAdd (![1, 2, 1, 2, 1, 2] i : ZMod 3))
        (Multiplicative.ofAdd (![1, 2, 1, 2, 1, 2] i : ZMod 3)) := by
  refine ⟨(⊤ : Subgroup (Multiplicative (ZMod 3))).subtype, by norm_num,
    (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩), ?_, ?_⟩
  · intro h
    simp only [Units.val_one, one_mul]
  · intro i
    exact IsConj.refl _

/-- The numerical supplier is constructed with positive even dimension and an empty
exponent list; this does not reconstruct its subgroup or its occurrence in the identity. -/
example : ∃ q : ℕ, 8 * (39191040 : ℤ) = 4374 * (2 * q - 2) ∧
    (2 * q - 2 : ℤ) = 71680 ∧ SupplierAdmissible 3 q [] := by
  refine ⟨35841, by norm_num, by norm_num, ?_⟩
  exact ⟨by norm_num, ⟨35840, by norm_num⟩, ⟨[], List.Perm.refl _, by simp⟩⟩

/-- Concrete nonzero norm witnesses for the two changes of discriminant representative. -/
example : SameNormClass 3 (-45) (-5) ∧ SameNormClass 3 (-396) (-11) := by
  exact ⟨⟨3, 0, by norm_num, by norm_num⟩, ⟨6, 0, by norm_num, by norm_num⟩⟩

/-- info: 'HodgeLean.Papers.skelg34_norm_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms skelg34_norm_descent

/-- info: 'HodgeLean.Papers.skelg34_not_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms skelg34_not_norm

/-- info: 'HodgeLean.Papers.skelg34_typeIII_classes_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms skelg34_typeIII_classes_aux

/-- info: 'HodgeLean.Papers.skelg34_typeIII_classes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms skelg34_typeIII_classes

end HodgeLean.Papers
