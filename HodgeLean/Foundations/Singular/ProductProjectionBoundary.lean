import HodgeLean.Foundations.Singular.ProductProjections

/-! The two total tensor differentials in specified bidegrees. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace HodgeLean.Foundations.Singular

/-- The first tensor differential projects to the first-factor boundary in the adjacent bidegree.
Source: Hatcher, Algebraic Topology, §3.2, the differential of the tensor complex. -/
theorem tensorD₁_projection (X Y : TopCat.{0}) (p q : ℕ) :
    HomologicalComplex.mapBifunctor.D₁ (rationalChains X) (rationalChains Y)
        (curriedTensor (ModuleCat ℚ)) (ComplexShape.down ℕ) (p + q + 1) (p + q) ≫
      tensorChainProjection X Y p q (p + q) =
    tensorChainProjection X Y (p + 1) q (p + q + 1) ≫
      ((rationalChains X).d (p + 1) p ▷ (rationalChains Y).X q) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro r s hrs
  change r + s = p + q + 1 at hrs
  rw [← Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁]
  cases r with
  | zero =>
    rw [HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ 0 s (p + q) (by simp),
      zero_comp, ← Category.assoc,
      tensorChainInclusion_projection_other X Y (p + 1) q 0 s (p + q + 1) hrs (by omega),
      zero_comp]
  | succ r =>
    rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (show (ComplexShape.down ℕ).Rel (r + 1) r by simp) s (p + q) (by dsimp; omega)]
    change ((1 : ℤˣ) • (((rationalChains X).d (r + 1) r ▷ (rationalChains Y).X s) ≫
      tensorChainInclusion X Y r s (p + q) (by omega))) ≫ _ = _
    rw [one_smul]
    by_cases hr : r = p
    · subst r
      have hs : s = q := by omega
      subst s
      rw [Category.assoc, tensorChainInclusion_projection_self,
        Category.comp_id, ← Category.assoc, tensorChainInclusion_projection_self]
      erw [Category.id_comp]
    · rw [Category.assoc,
        tensorChainInclusion_projection_other X Y p q r s (p + q) (by omega) (by omega),
        comp_zero, ← Category.assoc,
        tensorChainInclusion_projection_other X Y (p + 1) q (r + 1) s (p + q + 1) hrs (by omega),
        zero_comp]

/-- The second tensor differential projects to the signed second-factor boundary.
Source: Hatcher, Algebraic Topology, §3.2, the differential of the tensor complex. -/
theorem tensorD₂_projection (X Y : TopCat.{0}) (p q : ℕ) :
    HomologicalComplex.mapBifunctor.D₂ (rationalChains X) (rationalChains Y)
        (curriedTensor (ModuleCat ℚ)) (ComplexShape.down ℕ) (p + q + 1) (p + q) ≫
      tensorChainProjection X Y p q (p + q) =
    ((-1 : ℤˣ) ^ p) •
      (tensorChainProjection X Y p (q + 1) (p + q + 1) ≫
        ((rationalChains X).X p ◁ (rationalChains Y).d (q + 1) q)) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro r s hrs
  change r + s = p + q + 1 at hrs
  rw [← Category.assoc, HomologicalComplex.mapBifunctor.ι_D₂, Linear.comp_units_smul]
  cases s with
  | zero =>
    rw [HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ r 0 (p + q) (by simp),
      zero_comp, ← Category.assoc,
      tensorChainInclusion_projection_other X Y p (q + 1) r 0 (p + q + 1) hrs (by omega),
      zero_comp, smul_zero]
  | succ s =>
    rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ r
      (show (ComplexShape.down ℕ).Rel (s + 1) s by simp) (p + q) (by dsimp; omega)]
    change (((-1 : ℤˣ) ^ r) • (((rationalChains X).X r ◁ (rationalChains Y).d (s + 1) s) ≫
      tensorChainInclusion X Y r s (p + q) (by omega))) ≫ _ = _
    rw [Linear.units_smul_comp, Category.assoc]
    by_cases hr : r = p
    · subst r
      have hs : s = q := by omega
      subst s
      rw [tensorChainInclusion_projection_self, Category.comp_id,
        ← Category.assoc, tensorChainInclusion_projection_self]
      erw [Category.id_comp]
    · rw [tensorChainInclusion_projection_other X Y p q r s (p + q) (by omega) (by omega),
        comp_zero, ← Category.assoc,
        tensorChainInclusion_projection_other X Y p (q + 1) r (s + 1) (p + q + 1) hrs (by omega),
        zero_comp, smul_zero, smul_zero]

/-- The total tensor boundary has the two specified adjacent-bidegree components.
Source: Hatcher, Algebraic Topology, §3.2, the differential of the tensor complex. -/
theorem tensorChain_boundary_projection (X Y : TopCat.{0}) (p q : ℕ) :
    (rationalTensorChains X Y).d (p + q + 1) (p + q) ≫
      tensorChainProjection X Y p q (p + q) =
    tensorChainProjection X Y (p + 1) q (p + q + 1) ≫
        ((rationalChains X).d (p + 1) p ▷ (rationalChains Y).X q) +
      ((-1 : ℤˣ) ^ p) •
        (tensorChainProjection X Y p (q + 1) (p + q + 1) ≫
          ((rationalChains X).X p ◁ (rationalChains Y).d (q + 1) q)) := by
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.add_comp,
    tensorD₁_projection, tensorD₂_projection]

#print axioms tensorChain_boundary_projection
#print axioms tensorD₂_projection
#print axioms tensorD₁_projection
end HodgeLean.Foundations.Singular
