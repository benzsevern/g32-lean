import HodgeLean.Foundations.Singular.RationalTensorHomology

/-! Vanishing differentials in the tensor of actual rational homology quotient complexes. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace HodgeLean.Foundations.Singular

/-- The tensor of the actual zero-differential rational homology complexes has zero differential.
Source: Hatcher, Algebraic Topology, §3.2, the field-coefficient algebraic Künneth argument. -/
theorem rationalTensorHomology_d_eq_zero (K L : ChainComplex (ModuleCat ℚ) ℕ) (i j : ℕ) :
    (HomologicalComplex.tensorObj (rationalHomologyComplex K) (rationalHomologyComplex L)).d i j = 0 := by
  let A := rationalHomologyComplex K
  let B := rationalHomologyComplex L
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂, comp_zero]
  have h₁ : HomologicalComplex.mapBifunctor.d₁ A B
      (curriedTensor (ModuleCat ℚ)) (ComplexShape.down ℕ) p q j = 0 := by
    cases p with
    | zero => exact HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ 0 q j (by simp)
    | succ p =>
      rw [HomologicalComplex.mapBifunctor.d₁_eq' _ _ _ _
        (show (ComplexShape.down ℕ).Rel (p + 1) p by simp) q j,
        show A.d (p + 1) p = 0 from rfl]
      simp only [Functor.map_zero, zero_app, zero_comp, smul_zero]
  have h₂ : HomologicalComplex.mapBifunctor.d₂ A B
      (curriedTensor (ModuleCat ℚ)) (ComplexShape.down ℕ) p q j = 0 := by
    cases q with
    | zero => exact HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ p 0 j (by simp)
    | succ q =>
      rw [HomologicalComplex.mapBifunctor.d₂_eq' _ _ _ _ p
        (show (ComplexShape.down ℕ).Rel (q + 1) q by simp) j,
        show B.d (q + 1) q = 0 from rfl]
      simp only [Functor.map_zero, zero_comp, smul_zero]
  change HomologicalComplex.mapBifunctor.d₁ A B
      (curriedTensor (ModuleCat ℚ)) (ComplexShape.down ℕ) p q j +
    HomologicalComplex.mapBifunctor.d₂ A B
      (curriedTensor (ModuleCat ℚ)) (ComplexShape.down ℕ) p q j = 0
  rw [h₁, h₂, add_zero]

#print axioms rationalTensorHomology_d_eq_zero
end HodgeLean.Foundations.Singular
