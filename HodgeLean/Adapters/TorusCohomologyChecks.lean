import HodgeLean.Adapters.AbelianMilestones
import HodgeLean.Foundations.ProjectivePoint

/-! # Falsification checks for S13
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Singular
namespace HodgeLean.Adapters
variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

/-- Every abelian Betti number is the binomial coefficient for its real torus.
Source: `abelianTorusComparison` and `finrank_cohomology_unitAddTorus`. -/
theorem finrank_HQ_abelian (m : ℕ) :
    Module.finrank ℚ (HQ X m) = (2 * dim X.left).choose m := by
  rw [(abelianTorusComparison X m).finrank_eq, finrank_cohomology_unitAddTorus]

/-- An elliptic curve has two independent rational degree-one classes.
Source: `finrank_HQ_abelian`, degree one and complex dimension one. -/
theorem finrank_HQ_one_elliptic (hg : dim X.left = 1) :
    Module.finrank ℚ (HQ X 1) = 2 := by rw [finrank_HQ_abelian, hg]; norm_num

/-- The top rational cohomology of an elliptic curve is a line.
Source: `finrank_HQ_abelian`, degree two and complex dimension one. -/
theorem finrank_HQ_two_elliptic (hg : dim X.left = 1) :
    Module.finrank ℚ (HQ X 2) = 1 := by rw [finrank_HQ_abelian, hg]; norm_num

/-- In complex dimension zero the Betti sequence is one followed by zeroes.
Source: `finrank_HQ_abelian`, including the empty torus. -/
theorem finrank_HQ_abelian_zero (hg : dim X.left = 0) :
    Module.finrank ℚ (HQ X 0) = 1 ∧
      ∀ m : ℕ, Module.finrank ℚ (HQ X (m + 1)) = 0 := by
  simp [finrank_HQ_abelian, hg]

omit [GrpObj X] in
/-- Degree one is the identity after the canonical identification of the first exterior power.
Source: `RealDefs.CupProduct.cupWedgeMap_one`. -/
theorem cupWedgeMap_one_abelian :
    (cupProductOf X).cupWedgeMap 1 = (exteriorPower.oneEquiv ℚ (HQ X 1)).toLinearMap :=
  (cupProductOf X).cupWedgeMap_one

example (hg : dim X.left = 1) :
    Module.finrank ℚ (HQ X 1) = 2 ∧ Module.finrank ℚ (HQ X 2) = 1 :=
  ⟨finrank_HQ_one_elliptic X hg, finrank_HQ_two_elliptic X hg⟩
example (hg : dim X.left = 0) : Module.finrank ℚ (HQ X 3) = 0 :=
  (finrank_HQ_abelian_zero X hg).2 2
example (v : HQ X 1) : (cupProductOf X).cupWedgeMap 1
    ((exteriorPower.oneEquiv ℚ (HQ X 1)).symm v) = v := by
  rw [cupWedgeMap_one_abelian]; exact LinearEquiv.apply_symm_apply _ _

#print axioms torusCohomology_cupProductOf
#print axioms finiteBetti_abelian
#print axioms vanishingAboveTop_abelian
#print axioms hardLefschetz_abelian
#print axioms finrank_HQ_one_elliptic
#print axioms finrank_HQ_two_elliptic
#print axioms finrank_HQ_abelian_zero
#print axioms cupWedgeMap_one_abelian
section Point
open CategoryTheory.MonoidalCategory
private abbrev point : Over (Spec ↧ℂ) := 𝟙_ (Over (Spec ↧ℂ))
private instance : IsIntegral point.left := by
  change IsIntegral (Spec ↧ℂ)
  infer_instance
private instance : Smooth point.hom := by
  change Smooth (𝟙 (Spec ↧ℂ))
  infer_instance
private instance : IsProjective point.hom := by
  change IsProjective (𝟙 (Spec ↧ℂ))
  exact Foundations.isProjective_specComplex_id
private theorem point_dim : dim point.left = 0 := by
  have : SmoothOfRelativeDimension 0 point.hom := by
    change SmoothOfRelativeDimension 0 (𝟙 (Spec ↧ℂ))
    infer_instance
  exact SmoothOfRelativeDimension.dim_eq point.hom 0

example : Foundations.Symplectic.IsNondegenerate
    (((torusCohomology_cupProductOf point).cupWedgeEquiv 2).symm 0) ∧
    cupPow point (cupProductOf point) 0 (dim point.left) ≠ 0 :=
  nd_and_cupPow_of_dim_zero point (torusCohomology_cupProductOf point) point_dim 0

example : TorusCohomology (cupProductOf point) := torusCohomology_cupProductOf point
example : Module.finrank ℚ (HQ point 0) = 1 ∧
    ∀ m : ℕ, Module.finrank ℚ (HQ point (m + 1)) = 0 :=
  finrank_HQ_abelian_zero point point_dim
end Point
end HodgeLean.Adapters
