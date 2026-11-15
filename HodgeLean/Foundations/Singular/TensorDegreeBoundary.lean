import HodgeLean.Foundations.Singular.TensorDegreeProjections

/-! Bidegree projections of the actual differentials of arbitrary rational tensor complexes. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace HodgeLean.Foundations.Singular

/-- The first tensor differential projects to the first-factor boundary in the adjacent bidegree.
Source: Hatcher, Algebraic Topology, §3.2, the differential of the tensor complex. -/
theorem tensorDegreeD₁_projection (K L : ChainComplex (ModuleCat ℚ) ℕ) (p q : ℕ) :
    HomologicalComplex.mapBifunctor.D₁ (K) (L)
        (curriedTensor (ModuleCat ℚ)) (ComplexShape.down ℕ) (p + q + 1) (p + q) ≫
      tensorDegreeProjection K L p q (p + q) =
    tensorDegreeProjection K L (p + 1) q (p + q + 1) ≫
      ((K).d (p + 1) p ▷ (L).X q) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro r s hrs
  change r + s = p + q + 1 at hrs
  rw [← Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁]
  cases r with
  | zero =>
    rw [HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ 0 s (p + q) (by simp),
      zero_comp, ← Category.assoc,
      tensorDegreeInclusion_projection_other K L (p + 1) q 0 s (p + q + 1) hrs (by omega),
      zero_comp]
  | succ r =>
    rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (show (ComplexShape.down ℕ).Rel (r + 1) r by simp) s (p + q) (by dsimp; omega)]
    change ((1 : ℤˣ) • (((K).d (r + 1) r ▷ (L).X s) ≫
      HomologicalComplex.ιTensorObj K L r s (p + q) (by omega))) ≫ _ = _
    rw [one_smul]
    by_cases hr : r = p
    · subst r
      have hs : s = q := by omega
      subst s
      rw [Category.assoc, tensorDegreeInclusion_projection_self,
        Category.comp_id, ← Category.assoc, tensorDegreeInclusion_projection_self]
      erw [Category.id_comp]
    · rw [Category.assoc,
        tensorDegreeInclusion_projection_other K L p q r s (p + q) (by omega) (by omega),
        comp_zero, ← Category.assoc,
        tensorDegreeInclusion_projection_other K L (p + 1) q (r + 1) s (p + q + 1) hrs (by omega),
        zero_comp]

/-- The second tensor differential projects to the signed second-factor boundary.
Source: Hatcher, Algebraic Topology, §3.2, the differential of the tensor complex. -/
theorem tensorDegreeD₂_projection (K L : ChainComplex (ModuleCat ℚ) ℕ) (p q : ℕ) :
    HomologicalComplex.mapBifunctor.D₂ (K) (L)
        (curriedTensor (ModuleCat ℚ)) (ComplexShape.down ℕ) (p + q + 1) (p + q) ≫
      tensorDegreeProjection K L p q (p + q) =
    ((-1 : ℤˣ) ^ p) •
      (tensorDegreeProjection K L p (q + 1) (p + q + 1) ≫
        ((K).X p ◁ (L).d (q + 1) q)) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro r s hrs
  change r + s = p + q + 1 at hrs
  rw [← Category.assoc, HomologicalComplex.mapBifunctor.ι_D₂, Linear.comp_units_smul]
  cases s with
  | zero =>
    rw [HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ r 0 (p + q) (by simp),
      zero_comp, ← Category.assoc,
      tensorDegreeInclusion_projection_other K L p (q + 1) r 0 (p + q + 1) hrs (by omega),
      zero_comp, smul_zero]
  | succ s =>
    rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ r
      (show (ComplexShape.down ℕ).Rel (s + 1) s by simp) (p + q) (by dsimp; omega)]
    change (((-1 : ℤˣ) ^ r) • (((K).X r ◁ (L).d (s + 1) s) ≫
      HomologicalComplex.ιTensorObj K L r s (p + q) (by omega))) ≫ _ = _
    rw [Linear.units_smul_comp, Category.assoc]
    by_cases hr : r = p
    · subst r
      have hs : s = q := by omega
      subst s
      rw [tensorDegreeInclusion_projection_self, Category.comp_id,
        ← Category.assoc, tensorDegreeInclusion_projection_self]
      erw [Category.id_comp]
    · rw [tensorDegreeInclusion_projection_other K L p q r s (p + q) (by omega) (by omega),
        comp_zero, ← Category.assoc,
        tensorDegreeInclusion_projection_other K L p (q + 1) r (s + 1) (p + q + 1) hrs (by omega),
        zero_comp, smul_zero, smul_zero]

/-- The total tensor boundary has the two specified adjacent-bidegree components.
Source: Hatcher, Algebraic Topology, §3.2, the differential of the tensor complex. -/
theorem tensorDegree_boundary_projection (K L : ChainComplex (ModuleCat ℚ) ℕ) (p q : ℕ) :
    (HomologicalComplex.tensorObj K L).d (p + q + 1) (p + q) ≫
      tensorDegreeProjection K L p q (p + q) =
    tensorDegreeProjection K L (p + 1) q (p + q + 1) ≫
        ((K).d (p + 1) p ▷ (L).X q) +
      ((-1 : ℤˣ) ^ p) •
        (tensorDegreeProjection K L p (q + 1) (p + q + 1) ≫
          ((K).X p ◁ (L).d (q + 1) q)) := by
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.add_comp,
    tensorDegreeD₁_projection, tensorDegreeD₂_projection]

#print axioms tensorDegree_boundary_projection
#print axioms tensorDegreeD₂_projection
#print axioms tensorDegreeD₁_projection
end HodgeLean.Foundations.Singular
