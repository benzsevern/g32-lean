import HodgeLean.Foundations.Program.G32Native.PairedConormalRegularEvaluation
import HodgeLean.Foundations.Program.SchoenCycleS3PolynomialPoints
import HodgeLean.Foundations.Program.G32Native.PairedConormalGradedAffineEvaluation
import HodgeLean.Ported.NYLL.SchemeTheory.ProjectiveSpace.TwistingSheafHomogeneousRatios

/-! # Actual polynomial evaluation point arrows in specified normalized charts -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual scheme arrow evaluating a specified normalized complex polynomial chart. -/
def conormalPolynomialChartPoint {k : ℕ} (v : CoordinateSpace k)
    (i : Fin (k + 1)) (hi : v i ≠ 0) :
    Spec (CommRingCat.of ℂ) ⟶ Proj (homogeneousSubmodule (Fin (k + 1)) ℂ) :=
  Spec.map (CommRingCat.ofHom (s2e_complexPolynomialChartEvaluation v (X i)
    (by simpa only [eval_X] using hi))) ≫
      Proj.awayι (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i)
        (isHomogeneous_X ℂ i) zero_lt_one

/-- The actual evaluation arrow factors through its specified nonvanishing coordinate chart. -/
theorem conormal_polynomial_chart_point_preimage {k : ℕ} (v : CoordinateSpace k)
    (i : Fin (k + 1)) (hi : v i ≠ 0) :
    (⊤ : (Spec (CommRingCat.of ℂ)).Opens) ≤
      conormalPolynomialChartPoint v i hi ⁻¹ᵁ ProjSpace.standardOpen ℂ k i := by
  intro x _
  change Proj.awayι (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i)
    (isHomogeneous_X ℂ i) zero_lt_one
      ((Spec.map (CommRingCat.ofHom (s2e_complexPolynomialChartEvaluation v (X i)
        (by simpa only [eval_X] using hi)))) x) ∈
          Proj.basicOpen (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i)
  rw [← Proj.opensRange_awayι (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i)
    (isHomogeneous_X ℂ i) zero_lt_one]
  exact ⟨_, rfl⟩

/-- The actual regular homogeneous-ratio section evaluates to its literal numerator
value divided by the specified coordinate power along the supplied scheme arrow. -/
theorem conormal_polynomial_chart_point_homogeneous_ratio {k : ℕ}
    (v : CoordinateSpace k) (i : Fin (k + 1)) (hi : v i ≠ 0) (d : ℕ)
    (p : homogeneousSubmodule (Fin (k + 1)) ℂ d) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((conormalPolynomialChartPoint v i hi).appLE (ProjSpace.standardOpen ℂ k i) ⊤
        (conormal_polynomial_chart_point_preimage v i hi)
        (ProjSpace.homogeneousRatioSection ℂ k d p i)) =
      eval v p.val * (v i)⁻¹ ^ d := by
  have h := conormal_graded_affine_fraction_evaluation
    (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i) (isHomogeneous_X ℂ i) zero_lt_one
    (s2e_complexPolynomialChartEvaluation v (X i) (by simpa only [eval_X] using hi))
    (conormal_polynomial_chart_point_preimage v i hi)
  have hv := ConcreteCategory.congr_hom h
    (Away.mk (homogeneousSubmodule (Fin (k + 1)) ℂ) (isHomogeneous_X ℂ i) d p.val
      (by simpa using p.property))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at hv
  have hp : p.val.IsHomogeneous d := (mem_homogeneousSubmodule d _).mp p.property
  rw [s2e_complexPolynomialChartEvaluation_mk (hp := by simpa only [mul_one] using hp)] at hv
  simp only [eval_X] at hv
  convert! hv using 1

/-- The actual normalized evaluation arrow gives the same original homogeneous projective point. -/
theorem conormal_polynomial_chart_point_original {k : ℕ}
    (v : CoordinateSpace k) (i : Fin (k + 1)) (hi : v i ≠ 0) :
    conormalPolynomialChartPoint v i hi ≫
      (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom =
        vectorToProjectiveSpace v (vector_ne_zero_of_coordinate v i hi) := by
  let F (s : MvPolynomial (Fin (k + 1)) ℂ) (hs : eval v s ≠ 0)
      (hd : s ∈ homogeneousSubmodule (Fin (k + 1)) ℂ 1) :=
    Spec.map (CommRingCat.ofHom (s2e_complexPolynomialChartEvaluation v s hs)) ≫
      Proj.awayι (homogeneousSubmodule (Fin (k + 1)) ℂ) s hd zero_lt_one
  have heq (s t : MvPolynomial (Fin (k + 1)) ℂ) (hs : eval v s ≠ 0)
      (ht : eval v t ≠ 0) (hsd : s ∈ homogeneousSubmodule (Fin (k + 1)) ℂ 1)
      (htd : t ∈ homogeneousSubmodule (Fin (k + 1)) ℂ 1) (hst : s = t) :
      F s hs hsd = F t ht htd := by
    subst t
    rfl
  have hmap := heq (s2_polynomialIntegralCoordinates ℂ (Fin (k + 1)) (X i)) (X i)
    (by rw [s2_polynomialIntegralCoordinates_X, eval_X]; exact hi)
    (by simpa only [eval_X] using hi)
    ((s2_polynomialIntegralCoordinates ℂ (Fin (k + 1))).map_mem (isHomogeneous_X _ i))
    (isHomogeneous_X ℂ i) (s2_polynomialIntegralCoordinates_X ℂ (Fin (k + 1)) i)
  have h := s2e_complexPolynomialChartEvaluation_point v i hi
  rw [← Category.assoc] at h
  change F _ _ _ ≫ _ = _ at h
  erw [hmap] at h
  exact h

/-- The normalized polynomial evaluation arrow as an actual complex point for the specified model base. -/
def conormalPolynomialChartComplexPoint {k : ℕ}
    (v : CoordinateSpace k) (i : Fin (k + 1)) (hi : v i ≠ 0) :
    ComplexPoint (Over.mk ((s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom ≫
      ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) :=
  Over.homMk (conormalPolynomialChartPoint v i hi) (by
    change conormalPolynomialChartPoint v i hi ≫
      ((s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom ≫
        ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) = 𝟙 _
    rw [← Category.assoc, conormal_polynomial_chart_point_original,
      vectorToProjectiveSpace_toBase])

/-- The same actual complex point lies in the prescribed denominator chart. -/
theorem conormal_polynomial_chart_complex_point_mem {k : ℕ}
    (v : CoordinateSpace k) (i : Fin (k + 1)) (hi : v i ≠ 0) :
    conormalPolynomialChartComplexPoint v i hi ∈ Point.overOpen (ProjSpace.standardOpen ℂ k i) := by
  exact conormal_polynomial_chart_point_preimage v i hi trivial

/-- Actual regular evaluation at the same complex point gives the literal homogeneous fraction value. -/
theorem conormal_polynomial_chart_complex_point_evaluate {k : ℕ}
    (v : CoordinateSpace k) (i : Fin (k + 1)) (hi : v i ≠ 0) (d : ℕ)
    (p : homogeneousSubmodule (Fin (k + 1)) ℂ d) :
    Point.evaluate (ProjSpace.standardOpen ℂ k i)
      (ProjSpace.homogeneousRatioSection ℂ k d p i)
      (conormalPolynomialChartComplexPoint v i hi) = eval v p.val * (v i)⁻¹ ^ d := by
  have h := conormal_regular_evaluation_eq_appLE
    (Q := Over.mk ((s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom ≫
      ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) (ProjSpace.standardOpen ℂ k i)
    (ProjSpace.homogeneousRatioSection ℂ k d p i) (conormalPolynomialChartComplexPoint v i hi)
    (conormal_polynomial_chart_point_preimage v i hi)
  exact h.trans (conormal_polynomial_chart_point_homogeneous_ratio v i hi d p)

end HodgeLean.Foundations.Program.G32Native
